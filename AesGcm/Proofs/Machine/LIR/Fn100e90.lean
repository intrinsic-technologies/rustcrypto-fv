import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l100e90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e90 bytes_l100e90) (entryMap (live .l100e90))
      9 0x100e90 bytes_l100e90 b_l100e90 := by
  have f0 : InstrSpec 0x100e90 [0x55] (PushPre 0x100e90 1) (pushR64Effect 0x100e90 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100e90 1 5).toInstrSpec (push_r64_effect_step 0x100e90 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x100e91 [0x41, 0x57] (PushPre 0x100e91 2) (pushR64Effect 0x100e91 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100e91 2 15).toInstrSpec (push_r64_rex_effect_step 0x100e91 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100e93 [0x41, 0x56] (PushPre 0x100e93 2) (pushR64Effect 0x100e93 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100e93 2 14).toInstrSpec (push_r64_rex_effect_step 0x100e93 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100e95 [0x41, 0x55] (PushPre 0x100e95 2) (pushR64Effect 0x100e95 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100e95 2 13).toInstrSpec (push_r64_rex_effect_step 0x100e95 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100e97 [0x41, 0x54] (PushPre 0x100e97 2) (pushR64Effect 0x100e97 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100e97 2 12).toInstrSpec (push_r64_rex_effect_step 0x100e97 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100e99 [0x53] (PushPre 0x100e99 1) (pushR64Effect 0x100e99 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100e99 1 3).toInstrSpec (push_r64_effect_step 0x100e99 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x100e9a [0x48, 0x83, 0xEC, 0x68] (fun s => s.RIP = 0x100e9a) (subR64Imm8Effect 0x100e9a 4 0x68)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x100e9a 4 0x68).toInstrSpec (sub_r64_imm8_effect_step 0x100e9a 0x48 0xec 0x68 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100e9e [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x100e9e) (testR64R64Effect 0x100e9e 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100e9e 6 6).toInstrSpec (test_r64_r64_effect_step 0x100e9e 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e91) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e93) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e95) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e97) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e99) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e9a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100e9e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ea1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel32_effect_step 0x100ea1 4 0x2d0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100e90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e90 :=
  Rest.liftedBlock (rest_l100e90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e90 x hx)

theorem rest_l100ea7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ea7 bytes_l100ea7) (entryMap (live .l100ea7))
      2 0x100ea7 bytes_l100ea7 b_l100ea7 := by
  have f0 : InstrSpec 0x100ea7 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x100ea7) (cmpR64Imm8Effect 0x100ea7 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100ea7 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x100ea7 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100eab 4 0x2d6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100ea7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ea7 :=
  Rest.liftedBlock (rest_l100ea7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ea7 x hx)

theorem rest_l100eb1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100eb1 bytes_l100eb1) (entryMap (live .l100eb1))
      2 0x100eb1 bytes_l100eb1 b_l100eb1 := by
  have f0 : InstrSpec 0x100eb1 [0x48, 0x83, 0xFE, 0x02] (fun s => s.RIP = 0x100eb1) (cmpR64Imm8Effect 0x100eb1 6 0x2)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100eb1 6 0x2).toInstrSpec (cmp_r64_imm8_effect_step 0x100eb1 0x48 0xfe 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100eb5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x100eb5 6 0x2e2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100eb1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100eb1 :=
  Rest.liftedBlock (rest_l100eb1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100eb1 x hx)

theorem rest_l100ebb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ebb bytes_l100ebb) (entryMap (live .l100ebb))
      2 0x100ebb bytes_l100ebb b_l100ebb := by
  have f0 : InstrSpec 0x100ebb [0x48, 0x83, 0xFE, 0x03] (fun s => s.RIP = 0x100ebb) (cmpR64Imm8Effect 0x100ebb 6 0x3)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100ebb 6 0x3).toInstrSpec (cmp_r64_imm8_effect_step 0x100ebb 0x48 0xfe 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ebf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100ebf 4 0x2ee) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100ebb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ebb :=
  Rest.liftedBlock (rest_l100ebb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ebb x hx)

theorem rest_l100ec5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ec5 bytes_l100ec5) (entryMap (live .l100ec5))
      2 0x100ec5 bytes_l100ec5 b_l100ec5 := by
  have f0 : InstrSpec 0x100ec5 [0x48, 0x83, 0xFE, 0x04] (fun s => s.RIP = 0x100ec5) (cmpR64Imm8Effect 0x100ec5 6 0x4)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100ec5 6 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x100ec5 0x48 0xfe 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ec9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x100ec9 6 0x2fa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100ec5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ec5 :=
  Rest.liftedBlock (rest_l100ec5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ec5 x hx)

theorem rest_l100ecf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ecf bytes_l100ecf) (entryMap (live .l100ecf))
      2 0x100ecf bytes_l100ecf b_l100ecf := by
  have f0 : InstrSpec 0x100ecf [0x48, 0x83, 0xFE, 0x05] (fun s => s.RIP = 0x100ecf) (cmpR64Imm8Effect 0x100ecf 6 0x5)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100ecf 6 0x5).toInstrSpec (cmp_r64_imm8_effect_step 0x100ecf 0x48 0xfe 0x5 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ed3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100ed3 4 0x306) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100ecf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ecf :=
  Rest.liftedBlock (rest_l100ecf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ecf x hx)

theorem rest_l100ed9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ed9 bytes_l100ed9) (entryMap (live .l100ed9))
      2 0x100ed9 bytes_l100ed9 b_l100ed9 := by
  have f0 : InstrSpec 0x100ed9 [0x48, 0x83, 0xFE, 0x06] (fun s => s.RIP = 0x100ed9) (cmpR64Imm8Effect 0x100ed9 6 0x6)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100ed9 6 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x100ed9 0x48 0xfe 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100edd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x100edd 6 0x312) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100ed9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ed9 :=
  Rest.liftedBlock (rest_l100ed9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ed9 x hx)

theorem rest_l100ee3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100ee3 bytes_l100ee3) (entryMap (live .l100ee3))
      2 0x100ee3 bytes_l100ee3 b_l100ee3 := by
  have f0 : InstrSpec 0x100ee3 [0x48, 0x83, 0xFE, 0x07] (fun s => s.RIP = 0x100ee3) (cmpR64Imm8Effect 0x100ee3 6 0x7)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100ee3 6 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x100ee3 0x48 0xfe 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ee7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100ee7 4 0x31e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100ee3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100ee3 :=
  Rest.liftedBlock (rest_l100ee3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100ee3 x hx)

theorem rest_l100eed_9 [Bindings] (code : CodeMap) :
    Rest (n := 391) code lifted (codeRange 0x100eed bytes_l100eed) [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x101156 bytes_l100eed_9 b_l100eed_9 := by
  have f180 : InstrSpec 0x101156 [0x49, 0x31, 0xDD] (fun s => s.RIP = 0x101156) (xorR64R64Effect 0x101156 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101156 13 3).toInstrSpec (xor_r64_r64_effect_step 0x101156 0x49 0xdd (by decide) (by decide)) pre_rip
  have f181 : InstrSpec 0x101159 [0x49, 0x31, 0xC5] (fun s => s.RIP = 0x101159) (xorR64R64Effect 0x101159 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101159 13 0).toInstrSpec (xor_r64_r64_effect_step 0x101159 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f182 : InstrSpec 0x10115c [0x4C, 0x89, 0x6F, 0x28] (StorePre 0x10115c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x10115c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10115c 13 (.base 7 (.d8 0x28)))
      [.gpr 13, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10115c 13 (.base 7 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10115c 0x4c (by decide) 5 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f183 : InstrSpec 0x101160 [0x4C, 0x89, 0x77, 0x30] (StorePre 0x101160 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x101160 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101160 14 (.base 7 (.d8 0x30)))
      [.gpr 14, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x101160 14 (.base 7 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x101160 0x4c (by decide) 6 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f184 : InstrSpec 0x101164 [0x48, 0x89, 0x77, 0x38] (StorePre 0x101164 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x101164 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101164 6 (.base 7 (.d8 0x38)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x101164 6 (.base 7 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x101164 0x48 (by decide) 6 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f185 : InstrSpec 0x101168 [0x48, 0x83, 0xC4, 0x68] (fun s => s.RIP = 0x101168) (addR64Imm8Effect 0x101168 4 0x68)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x101168 4 0x68).toInstrSpec (add_r64_imm8_effect_step 0x101168 0x48 0xc4 0x68 (by decide) (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x10116c [0x5B] (PopPre 0x10116c) (popR64Effect 0x10116c 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10116c 1 3).toInstrSpec (pop_r64_effect_step 0x10116c 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f187 : InstrSpec 0x10116d [0x41, 0x5C] (PopPre 0x10116d) (popR64Effect 0x10116d 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10116d 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10116d 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f188 : InstrSpec 0x10116f [0x41, 0x5D] (PopPre 0x10116f) (popR64Effect 0x10116f 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10116f 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10116f 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f189 : InstrSpec 0x101171 [0x41, 0x5E] (PopPre 0x101171) (popR64Effect 0x101171 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101171 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101171 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f190 : InstrSpec 0x101173 [0x41, 0x5F] (PopPre 0x101173) (popR64Effect 0x101173 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101173 2 15).toInstrSpec (pop_r64_rex_effect_step 0x101173 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f191 : InstrSpec 0x101175 [0x5D] (PopPre 0x101175) (popR64Effect 0x101175 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101175 1 5).toInstrSpec (pop_r64_effect_step 0x101175 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f192 : InstrSpec 0x101176 [0xC3] (RetPre 0x101176) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101176).toInstrSpec (ret_effect_step 0x101176) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f180 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 392) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 391), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101159) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 393) (RestInside.out (n := 393) f181 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 394) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 393), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10115c) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 395) (RestInside.exec (n := 395) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 393), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101160) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 396) (RestInside.exec (n := 396) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 393), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101164) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 397) (RestInside.exec (n := 397) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 393), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101168) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 398) (RestInside.out (n := 398) f185 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 399) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 398), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 393), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10116c) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 400) (RestInside.out (n := 400) f186 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 401) f186 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 402) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 400), (4, 401), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 393), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10116d) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.out (n := 403) f187 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 404) f187 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 405) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 400), (4, 404), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 403), (13, 393), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10116f) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.out (n := 406) f188 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 407) f188 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 408) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 400), (4, 407), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 403), (13, 406), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101171) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 409) (RestInside.out (n := 409) f189 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 410) f189 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 411) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 400), (4, 410), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 403), (13, 406), (14, 409), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101173) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.out (n := 412) f190 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 413) f190 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 414) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 400), (4, 413), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 403), (13, 406), (14, 409), (15, 412), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101175) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 415) (RestInside.out (n := 415) f191 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 416) f191 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 417) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 400), (4, 416), (5, 415), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 403), (13, 406), (14, 409), (15, 412), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101176) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.out (n := 418) f192 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 419) f192 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 420) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 400), (4, 419), (5, 415), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 403), (13, 406), (14, 409), (15, 412), (22, 22), (39, 39), (50, 50), (51, 51)]) f192 (by decide) rfl rfl rfl (by decide)

theorem rest_l100eed_8 [Bindings] (code : CodeMap) :
    Rest (n := 356) code lifted (codeRange 0x100eed bytes_l100eed) [(0, 288), (1, 338), (2, 348), (3, 350), (4, 4), (5, 290), (6, 344), (7, 7), (8, 354), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x101111 bytes_l100eed_8 b_l100eed_8 := by
  have f160 : InstrSpec 0x101111 [0x4D, 0x31, 0xD8] (fun s => s.RIP = 0x101111) (xorR64R64Effect 0x101111 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101111 8 11).toInstrSpec (xor_r64_r64_effect_step 0x101111 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x101114 [0x4D, 0x31, 0xD5] (fun s => s.RIP = 0x101114) (xorR64R64Effect 0x101114 13 10)
      [.gpr 13, .gpr 10] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101114 13 10).toInstrSpec (xor_r64_r64_effect_step 0x101114 0x4d 0xd5 (by decide) (by decide)) pre_rip
  have f162 : InstrSpec 0x101117 [0x48, 0x33, 0x54, 0x24, 0x20] (LoadPre 0x101117 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101117 + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x101117 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x101117 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (xor_r64_m64_effect_step 0x101117 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f163 : InstrSpec 0x10111c [0x48, 0x33, 0x14, 0x24] (LoadPre 0x10111c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10111c + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x10111c 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x10111c 2 (.sib 4 none 0 .none)).toInstrSpec (xor_r64_m64_effect_step 0x10111c 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f164 : InstrSpec 0x101120 [0x48, 0x31, 0xD5] (fun s => s.RIP = 0x101120) (xorR64R64Effect 0x101120 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101120 5 2).toInstrSpec (xor_r64_r64_effect_step 0x101120 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x101123 [0x48, 0x31, 0xCD] (fun s => s.RIP = 0x101123) (xorR64R64Effect 0x101123 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101123 5 1).toInstrSpec (xor_r64_r64_effect_step 0x101123 0x48 0xcd (by decide) (by decide)) pre_rip
  have f166 : InstrSpec 0x101126 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x101126 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x101126 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101126 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x101126 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x101126 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f167 : InstrSpec 0x10112b [0x4C, 0x31, 0xC0] (fun s => s.RIP = 0x10112b) (xorR64R64Effect 0x10112b 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10112b 0 8).toInstrSpec (xor_r64_r64_effect_step 0x10112b 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x10112e [0x49, 0x31, 0xE8] (fun s => s.RIP = 0x10112e) (xorR64R64Effect 0x10112e 8 5)
      [.gpr 8, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10112e 8 5).toInstrSpec (xor_r64_r64_effect_step 0x10112e 0x49 0xe8 (by decide) (by decide)) pre_rip
  have f169 : InstrSpec 0x101131 [0x4C, 0x31, 0xCD] (fun s => s.RIP = 0x101131) (xorR64R64Effect 0x101131 5 9)
      [.gpr 5, .gpr 9] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101131 5 9).toInstrSpec (xor_r64_r64_effect_step 0x101131 0x4c 0xcd (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x101134 [0x48, 0x89, 0x2F] (StorePre 0x101134 3 (fun s => AddrMode.addr (.base 7 .none) s (0x101134 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101134 5 (.base 7 .none))
      [.gpr 5, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x101134 5 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x101134 0x48 (by decide) 5 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f171 : InstrSpec 0x101137 [0x4C, 0x89, 0x47, 0x08] (StorePre 0x101137 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x101137 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101137 8 (.base 7 (.d8 0x8)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x101137 8 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x101137 0x4c (by decide) 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f172 : InstrSpec 0x10113b [0x49, 0x31, 0xC7] (fun s => s.RIP = 0x10113b) (xorR64R64Effect 0x10113b 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10113b 15 0).toInstrSpec (xor_r64_r64_effect_step 0x10113b 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f173 : InstrSpec 0x10113e [0x4C, 0x89, 0x7F, 0x10] (StorePre 0x10113e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10113e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10113e 15 (.base 7 (.d8 0x10)))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10113e 15 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10113e 0x4c (by decide) 7 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f174 : InstrSpec 0x101142 [0x49, 0x31, 0xF6] (fun s => s.RIP = 0x101142) (xorR64R64Effect 0x101142 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101142 14 6).toInstrSpec (xor_r64_r64_effect_step 0x101142 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x101145 [0x4C, 0x31, 0xF2] (fun s => s.RIP = 0x101145) (xorR64R64Effect 0x101145 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101145 2 14).toInstrSpec (xor_r64_r64_effect_step 0x101145 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f176 : InstrSpec 0x101148 [0x48, 0x89, 0x57, 0x18] (StorePre 0x101148 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x101148 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101148 2 (.base 7 (.d8 0x18)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x101148 2 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x101148 0x48 (by decide) 2 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f177 : InstrSpec 0x10114c [0x48, 0x31, 0xDE] (fun s => s.RIP = 0x10114c) (xorR64R64Effect 0x10114c 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10114c 6 3).toInstrSpec (xor_r64_r64_effect_step 0x10114c 0x48 0xde (by decide) (by decide)) pre_rip
  have f178 : InstrSpec 0x10114f [0x4C, 0x89, 0x77, 0x20] (StorePre 0x10114f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10114f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10114f 14 (.base 7 (.d8 0x20)))
      [.gpr 14, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x10114f 14 (.base 7 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10114f 0x4c (by decide) 6 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f179 : InstrSpec 0x101153 [0x49, 0x31, 0xDE] (fun s => s.RIP = 0x101153) (xorR64R64Effect 0x101153 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101153 14 3).toInstrSpec (xor_r64_r64_effect_step 0x101153 0x49 0xde (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 356) (RestInside.out (n := 356) f160 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 357) (ρ' := [(0, 288), (1, 338), (2, 348), (3, 350), (4, 4), (5, 290), (6, 344), (7, 7), (8, 356), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101114) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 358) (RestInside.out (n := 358) f161 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 359) (ρ' := [(0, 288), (1, 338), (2, 348), (3, 350), (4, 4), (5, 290), (6, 344), (7, 7), (8, 356), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101117) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 360) (RestInside.out (n := 360) f162 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 361) (ρ' := [(0, 288), (1, 338), (2, 360), (3, 350), (4, 4), (5, 290), (6, 344), (7, 7), (8, 356), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10111c) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 362) (RestInside.out (n := 362) f163 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 363) (ρ' := [(0, 288), (1, 338), (2, 362), (3, 350), (4, 4), (5, 290), (6, 344), (7, 7), (8, 356), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101120) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 364) (RestInside.out (n := 364) f164 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 365) (ρ' := [(0, 288), (1, 338), (2, 362), (3, 350), (4, 4), (5, 364), (6, 344), (7, 7), (8, 356), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101123) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 366) (RestInside.out (n := 366) f165 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 367) (ρ' := [(0, 288), (1, 338), (2, 362), (3, 350), (4, 4), (5, 366), (6, 344), (7, 7), (8, 356), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101126) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 368) (RestInside.out (n := 368) f166 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 369) (ρ' := [(0, 368), (1, 338), (2, 362), (3, 350), (4, 4), (5, 366), (6, 344), (7, 7), (8, 356), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10112b) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 370) (RestInside.out (n := 370) f167 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 371) (ρ' := [(0, 370), (1, 338), (2, 362), (3, 350), (4, 4), (5, 366), (6, 344), (7, 7), (8, 356), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10112e) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 372) (RestInside.out (n := 372) f168 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 373) (ρ' := [(0, 370), (1, 338), (2, 362), (3, 350), (4, 4), (5, 366), (6, 344), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101131) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 374) (RestInside.out (n := 374) f169 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 375) (ρ' := [(0, 370), (1, 338), (2, 362), (3, 350), (4, 4), (5, 374), (6, 344), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101134) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 376) (RestInside.exec (n := 376) (ρ' := [(0, 370), (1, 338), (2, 362), (3, 350), (4, 4), (5, 374), (6, 344), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101137) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 377) (RestInside.exec (n := 377) (ρ' := [(0, 370), (1, 338), (2, 362), (3, 350), (4, 4), (5, 374), (6, 344), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10113b) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f172 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 370), (1, 338), (2, 362), (3, 350), (4, 4), (5, 374), (6, 344), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10113e) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.exec (n := 380) (ρ' := [(0, 370), (1, 338), (2, 362), (3, 350), (4, 4), (5, 374), (6, 344), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 314), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101142) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 381) (RestInside.out (n := 381) f174 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 382) (ρ' := [(0, 370), (1, 338), (2, 362), (3, 350), (4, 4), (5, 374), (6, 344), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 381), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101145) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 383) (RestInside.out (n := 383) f175 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 384) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 344), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 381), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101148) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 385) (RestInside.exec (n := 385) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 344), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 381), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10114c) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 386) (RestInside.out (n := 386) f177 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 387) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 381), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10114f) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 388) (RestInside.exec (n := 388) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 381), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101153) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f179 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 370), (1, 338), (2, 383), (3, 350), (4, 4), (5, 374), (6, 386), (7, 7), (8, 372), (9, 278), (10, 310), (11, 324), (12, 284), (13, 358), (14, 389), (15, 378), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101156) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100eed_9 code

theorem rest_l100eed_7 [Bindings] (code : CodeMap) :
    Rest (n := 316) code lifted (codeRange 0x100eed bytes_l100eed) [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 227), (12, 284), (13, 259), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]
      53 0x1010c9 bytes_l100eed_7 b_l100eed_7 := by
  have f140 : InstrSpec 0x1010c9 [0x49, 0x31, 0xD5] (fun s => s.RIP = 0x1010c9) (xorR64R64Effect 0x1010c9 13 2)
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010c9 13 2).toInstrSpec (xor_r64_r64_effect_step 0x1010c9 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x1010cc [0x4C, 0x31, 0xE9] (fun s => s.RIP = 0x1010cc) (xorR64R64Effect 0x1010cc 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010cc 1 13).toInstrSpec (xor_r64_r64_effect_step 0x1010cc 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x1010cf [0x4C, 0x8B, 0x5C, 0x24, 0x50] (LoadPre 0x1010cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1010cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010cf 11 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1010cf 11 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1010cf 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f143 : InstrSpec 0x1010d4 [0x49, 0x21, 0xCB] (fun s => s.RIP = 0x1010d4) (andR64R64Effect 0x1010d4 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1010d4 11 1).toInstrSpec (and_r64_r64_effect_step 0x1010d4 0x49 0xcb (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x1010d7 [0x4D, 0x31, 0xFB] (fun s => s.RIP = 0x1010d7) (xorR64R64Effect 0x1010d7 11 15)
      [.gpr 11, .gpr 15] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010d7 11 15).toInstrSpec (xor_r64_r64_effect_step 0x1010d7 0x4d 0xfb (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x1010da [0x48, 0x23, 0x4C, 0x24, 0x58] (LoadPre 0x1010da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1010da + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x1010da 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (andR64M64Effect_footprint 0x1010da 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (and_r64_m64_effect_step 0x1010da 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f146 : InstrSpec 0x1010df [0x48, 0x8B, 0x5C, 0x24, 0x48] (LoadPre 0x1010df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1010df + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010df 3 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1010df 3 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x1010df 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f147 : InstrSpec 0x1010e4 [0x4C, 0x21, 0xEB] (fun s => s.RIP = 0x1010e4) (andR64R64Effect 0x1010e4 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1010e4 3 13).toInstrSpec (and_r64_r64_effect_step 0x1010e4 0x4c 0xeb (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x1010e7 [0x4C, 0x23, 0x6C, 0x24, 0x60] (LoadPre 0x1010e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1010e7 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x1010e7 13 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (andR64M64Effect_footprint 0x1010e7 13 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (and_r64_m64_effect_step 0x1010e7 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f149 : InstrSpec 0x1010ec [0x4C, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x1010ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1010ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010ec 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1010ec 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1010ec 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f150 : InstrSpec 0x1010f1 [0x49, 0x21, 0xD7] (fun s => s.RIP = 0x1010f1) (andR64R64Effect 0x1010f1 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1010f1 15 2).toInstrSpec (and_r64_r64_effect_step 0x1010f1 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x1010f4 [0x4C, 0x31, 0xE9] (fun s => s.RIP = 0x1010f4) (xorR64R64Effect 0x1010f4 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010f4 1 13).toInstrSpec (xor_r64_r64_effect_step 0x1010f4 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x1010f7 [0x48, 0x31, 0xCE] (fun s => s.RIP = 0x1010f7) (xorR64R64Effect 0x1010f7 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010f7 6 1).toInstrSpec (xor_r64_r64_effect_step 0x1010f7 0x48 0xce (by decide) (by decide)) pre_rip
  have f153 : InstrSpec 0x1010fa [0x49, 0x31, 0xF7] (fun s => s.RIP = 0x1010fa) (xorR64R64Effect 0x1010fa 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010fa 15 6).toInstrSpec (xor_r64_r64_effect_step 0x1010fa 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f154 : InstrSpec 0x1010fd [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x1010fd) (xorR64R64Effect 0x1010fd 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010fd 6 0).toInstrSpec (xor_r64_r64_effect_step 0x1010fd 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x101100 [0x48, 0x23, 0x54, 0x24, 0x40] (LoadPre 0x101100 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101100 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x101100 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (andR64M64Effect_footprint 0x101100 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (and_r64_m64_effect_step 0x101100 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f156 : InstrSpec 0x101105 [0x4C, 0x31, 0xE2] (fun s => s.RIP = 0x101105) (xorR64R64Effect 0x101105 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101105 2 12).toInstrSpec (xor_r64_r64_effect_step 0x101105 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x101108 [0x4C, 0x31, 0xDB] (fun s => s.RIP = 0x101108) (xorR64R64Effect 0x101108 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101108 3 11).toInstrSpec (xor_r64_r64_effect_step 0x101108 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f158 : InstrSpec 0x10110b [0x49, 0x31, 0xD0] (fun s => s.RIP = 0x10110b) (xorR64R64Effect 0x10110b 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10110b 8 2).toInstrSpec (xor_r64_r64_effect_step 0x10110b 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x10110e [0x4D, 0x31, 0xC8] (fun s => s.RIP = 0x10110e) (xorR64R64Effect 0x10110e 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10110e 8 9).toInstrSpec (xor_r64_r64_effect_step 0x10110e 0x4d 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f140 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 227), (12, 284), (13, 316), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010cc) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f141 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 288), (1, 318), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 227), (12, 284), (13, 316), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010cf) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f142 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 321) (ρ' := [(0, 288), (1, 318), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 320), (12, 284), (13, 316), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010d4) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f143 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 288), (1, 318), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 322), (12, 284), (13, 316), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010d7) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f144 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 288), (1, 318), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 316), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010da) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f145 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 288), (1, 326), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 316), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010df) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f146 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 329) (ρ' := [(0, 288), (1, 326), (2, 261), (3, 328), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 316), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010e4) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f147 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 288), (1, 326), (2, 261), (3, 330), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 316), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010e7) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f148 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 288), (1, 326), (2, 261), (3, 330), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010ec) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f149 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 335) (ρ' := [(0, 288), (1, 326), (2, 261), (3, 330), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 334), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010f1) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f150 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 288), (1, 326), (2, 261), (3, 330), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 336), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010f4) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f151 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 339) (ρ' := [(0, 288), (1, 338), (2, 261), (3, 330), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 336), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010f7) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 340) (RestInside.out (n := 340) f152 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 341) (ρ' := [(0, 288), (1, 338), (2, 261), (3, 330), (4, 4), (5, 290), (6, 340), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 336), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010fa) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.out (n := 342) f153 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 343) (ρ' := [(0, 288), (1, 338), (2, 261), (3, 330), (4, 4), (5, 290), (6, 340), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010fd) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f154 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 288), (1, 338), (2, 261), (3, 330), (4, 4), (5, 290), (6, 344), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101100) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.out (n := 346) f155 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 347) (ρ' := [(0, 288), (1, 338), (2, 346), (3, 330), (4, 4), (5, 290), (6, 344), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101105) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f156 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 349) (ρ' := [(0, 288), (1, 338), (2, 348), (3, 330), (4, 4), (5, 290), (6, 344), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101108) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 350) (RestInside.out (n := 350) f157 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 351) (ρ' := [(0, 288), (1, 338), (2, 348), (3, 350), (4, 4), (5, 290), (6, 344), (7, 7), (8, 306), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10110b) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 352) (RestInside.out (n := 352) f158 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 353) (ρ' := [(0, 288), (1, 338), (2, 348), (3, 350), (4, 4), (5, 290), (6, 344), (7, 7), (8, 352), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10110e) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 354) (RestInside.out (n := 354) f159 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 355) (ρ' := [(0, 288), (1, 338), (2, 348), (3, 350), (4, 4), (5, 290), (6, 344), (7, 7), (8, 354), (9, 278), (10, 310), (11, 324), (12, 284), (13, 332), (14, 314), (15, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101111) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100eed_8 code

theorem rest_l100eed_6 [Bindings] (code : CodeMap) :
    Rest (n := 278) code lifted (codeRange 0x100eed bytes_l100eed) [(0, 263), (1, 269), (2, 261), (3, 275), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 273), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]
      73 0x101081 bytes_l100eed_6 b_l100eed_6 := by
  have f120 : InstrSpec 0x101081 [0x4C, 0x23, 0x4C, 0x24, 0x10] (LoadPre 0x101081 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101081 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x101081 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (andR64M64Effect_footprint 0x101081 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (and_r64_m64_effect_step 0x101081 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x101086 [0x4C, 0x31, 0xD8] (fun s => s.RIP = 0x101086) (xorR64R64Effect 0x101086 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101086 0 11).toInstrSpec (xor_r64_r64_effect_step 0x101086 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x101089 [0x4C, 0x8B, 0x64, 0x24, 0x18] (LoadPre 0x101089 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101089 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101089 12 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x101089 12 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x101089 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f123 : InstrSpec 0x10108e [0x49, 0x21, 0xC4] (fun s => s.RIP = 0x10108e) (andR64R64Effect 0x10108e 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10108e 12 0).toInstrSpec (and_r64_r64_effect_step 0x10108e 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x101091 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x101091) (movR64R64Effect 0x101091 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101091 14 0).toInstrSpec (mov_r64_r64_effect_step 0x101091 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x101094 [0x48, 0x23, 0x44, 0x24, 0x28] (LoadPre 0x101094 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101094 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x101094 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (andR64M64Effect_footprint 0x101094 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (and_r64_m64_effect_step 0x101094 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f126 : InstrSpec 0x101099 [0x48, 0x21, 0xCD] (fun s => s.RIP = 0x101099) (andR64R64Effect 0x101099 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101099 5 1).toInstrSpec (and_r64_r64_effect_step 0x101099 0x48 0xcd (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x10109c [0x49, 0x21, 0xCF] (fun s => s.RIP = 0x10109c) (andR64R64Effect 0x10109c 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10109c 15 1).toInstrSpec (and_r64_r64_effect_step 0x10109c 0x49 0xcf (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x10109f [0x49, 0x31, 0xD6] (fun s => s.RIP = 0x10109f) (xorR64R64Effect 0x10109f 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10109f 14 2).toInstrSpec (xor_r64_r64_effect_step 0x10109f 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x1010a2 [0x4C, 0x31, 0xF1] (fun s => s.RIP = 0x1010a2) (xorR64R64Effect 0x1010a2 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010a2 1 14).toInstrSpec (xor_r64_r64_effect_step 0x1010a2 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x1010a5 [0x4C, 0x21, 0xF6] (fun s => s.RIP = 0x1010a5) (andR64R64Effect 0x1010a5 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1010a5 6 14).toInstrSpec (and_r64_r64_effect_step 0x1010a5 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x1010a8 [0x4D, 0x21, 0xD6] (fun s => s.RIP = 0x1010a8) (andR64R64Effect 0x1010a8 14 10)
      [.gpr 14, .gpr 10] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1010a8 14 10).toInstrSpec (and_r64_r64_effect_step 0x1010a8 0x4d 0xd6 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x1010ab [0x4C, 0x21, 0x6C, 0x24, 0x30] (StorePre 0x1010ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1010ab + BitVec.ofNat 64 5)) 8) (andMREffect 0x1010ab 5 64 13 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 13, .gpr 4] [] [.flags, .rip] :=
    (andMREffect64_footprint 0x1010ab 5 13 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (and_m64_r64_effect_step 0x1010ab 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f133 : InstrSpec 0x1010b0 [0x4C, 0x21, 0x6C, 0x24, 0x20] (StorePre 0x1010b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1010b0 + BitVec.ofNat 64 5)) 8) (andMREffect 0x1010b0 5 64 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 13, .gpr 4] [] [.flags, .rip] :=
    (andMREffect64_footprint 0x1010b0 5 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (and_m64_r64_effect_step 0x1010b0 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f134 : InstrSpec 0x1010b5 [0x49, 0x31, 0xDF] (fun s => s.RIP = 0x1010b5) (xorR64R64Effect 0x1010b5 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010b5 15 3).toInstrSpec (xor_r64_r64_effect_step 0x1010b5 0x49 0xdf (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x1010b8 [0x49, 0x21, 0xC8] (fun s => s.RIP = 0x1010b8) (andR64R64Effect 0x1010b8 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1010b8 8 1).toInstrSpec (and_r64_r64_effect_step 0x1010b8 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x1010bb [0x4C, 0x8B, 0x54, 0x24, 0x38] (LoadPre 0x1010bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1010bb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010bb 10 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1010bb 10 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1010bb 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f137 : InstrSpec 0x1010c0 [0x49, 0x21, 0xCA] (fun s => s.RIP = 0x1010c0) (andR64R64Effect 0x1010c0 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1010c0 10 1).toInstrSpec (and_r64_r64_effect_step 0x1010c0 0x49 0xca (by decide) (by decide)) pre_rip
  have f138 : InstrSpec 0x1010c3 [0x4D, 0x31, 0xE6] (fun s => s.RIP = 0x1010c3) (xorR64R64Effect 0x1010c3 14 12)
      [.gpr 14, .gpr 12] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010c3 14 12).toInstrSpec (xor_r64_r64_effect_step 0x1010c3 0x4d 0xe6 (by decide) (by decide)) pre_rip
  have f139 : InstrSpec 0x1010c6 [0x4D, 0x31, 0xFE] (fun s => s.RIP = 0x1010c6) (xorR64R64Effect 0x1010c6 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1010c6 14 15).toInstrSpec (xor_r64_r64_effect_step 0x1010c6 0x4d 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f120 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 263), (1, 269), (2, 261), (3, 275), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101086) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f121 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 280), (1, 269), (2, 261), (3, 275), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101089) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f122 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 280), (1, 269), (2, 261), (3, 275), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 282), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10108e) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f123 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 280), (1, 269), (2, 261), (3, 275), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101091) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f124 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 280), (1, 269), (2, 261), (3, 275), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 286), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101094) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f125 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 288), (1, 269), (2, 261), (3, 275), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 286), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101099) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f126 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 288), (1, 269), (2, 261), (3, 275), (4, 4), (5, 290), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 286), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10109c) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f127 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 288), (1, 269), (2, 261), (3, 275), (4, 4), (5, 290), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 286), (15, 292), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10109f) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f128 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 295) (ρ' := [(0, 288), (1, 269), (2, 261), (3, 275), (4, 4), (5, 290), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 294), (15, 292), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010a2) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.out (n := 296) f129 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 297) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 211), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 294), (15, 292), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010a5) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f130 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 294), (15, 292), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010a8) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f131 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 300), (15, 292), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010ab) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.exec (n := 302) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 300), (15, 292), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010b0) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 303) (RestInside.exec (n := 303) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 300), (15, 292), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010b5) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f134 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 114), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 300), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010b8) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f135 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 207), (11, 227), (12, 284), (13, 259), (14, 300), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010bb) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f136 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 308), (11, 227), (12, 284), (13, 259), (14, 300), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010c0) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f137 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 311) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 227), (12, 284), (13, 259), (14, 300), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010c3) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f138 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 227), (12, 284), (13, 259), (14, 312), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010c6) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f139 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 288), (1, 296), (2, 261), (3, 275), (4, 4), (5, 290), (6, 298), (7, 7), (8, 306), (9, 278), (10, 310), (11, 227), (12, 284), (13, 259), (14, 314), (15, 304), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010c9) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100eed_7 code

theorem rest_l100eed_5 [Bindings] (code : CodeMap) :
    Rest (n := 239) code lifted (codeRange 0x100eed bytes_l100eed) [(0, 237), (1, 191), (2, 235), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 129), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]
      93 0x101044 bytes_l100eed_5 b_l100eed_5 := by
  have f100 : InstrSpec 0x101044 [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x101044) (andR64R64Effect 0x101044 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101044 0 2).toInstrSpec (and_r64_r64_effect_step 0x101044 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x101047 [0x49, 0x89, 0xCC] (fun s => s.RIP = 0x101047) (movR64R64Effect 0x101047 12 1)
      [.gpr 1] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x101047 12 1).toInstrSpec (mov_r64_r64_effect_step 0x101047 0x49 0xcc (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x10104a [0x49, 0x31, 0xDC] (fun s => s.RIP = 0x10104a) (xorR64R64Effect 0x10104a 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10104a 12 3).toInstrSpec (xor_r64_r64_effect_step 0x10104a 0x49 0xdc (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x10104d [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x10104d) (movR64R64Effect 0x10104d 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10104d 2 0).toInstrSpec (mov_r64_r64_effect_step 0x10104d 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x101050 [0x4C, 0x31, 0xE8] (fun s => s.RIP = 0x101050) (xorR64R64Effect 0x101050 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101050 0 13).toInstrSpec (xor_r64_r64_effect_step 0x101050 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x101053 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x101053) (movR64R64Effect 0x101053 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x101053 1 13).toInstrSpec (mov_r64_r64_effect_step 0x101053 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x101056 [0x4C, 0x31, 0xE1] (fun s => s.RIP = 0x101056) (xorR64R64Effect 0x101056 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101056 1 12).toInstrSpec (xor_r64_r64_effect_step 0x101056 0x4c 0xe1 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x101059 [0x4D, 0x31, 0xF1] (fun s => s.RIP = 0x101059) (xorR64R64Effect 0x101059 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101059 9 14).toInstrSpec (xor_r64_r64_effect_step 0x101059 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x10105c [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x10105c) (movR64R64Effect 0x10105c 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10105c 13 1).toInstrSpec (mov_r64_r64_effect_step 0x10105c 0x49 0xcd (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x10105f [0x4D, 0x21, 0xCD] (fun s => s.RIP = 0x10105f) (andR64R64Effect 0x10105f 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10105f 13 9).toInstrSpec (and_r64_r64_effect_step 0x10105f 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x101062 [0x4D, 0x31, 0xF5] (fun s => s.RIP = 0x101062) (xorR64R64Effect 0x101062 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101062 13 14).toInstrSpec (xor_r64_r64_effect_step 0x101062 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x101065 [0x4C, 0x31, 0xE2] (fun s => s.RIP = 0x101065) (xorR64R64Effect 0x101065 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101065 2 12).toInstrSpec (xor_r64_r64_effect_step 0x101065 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x101068 [0x4C, 0x21, 0xE0] (fun s => s.RIP = 0x101068) (andR64R64Effect 0x101068 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101068 0 12).toInstrSpec (and_r64_r64_effect_step 0x101068 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x10106b [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10106b) (xorR64R64Effect 0x10106b 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10106b 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10106b 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x10106e [0x4C, 0x21, 0xE9] (fun s => s.RIP = 0x10106e) (andR64R64Effect 0x10106e 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10106e 1 13).toInstrSpec (and_r64_r64_effect_step 0x10106e 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x101071 [0x4C, 0x31, 0xC9] (fun s => s.RIP = 0x101071) (xorR64R64Effect 0x101071 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101071 1 9).toInstrSpec (xor_r64_r64_effect_step 0x101071 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x101074 [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x101074) (movR64R64Effect 0x101074 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x101074 9 1).toInstrSpec (mov_r64_r64_effect_step 0x101074 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x101077 [0x4D, 0x31, 0xE9] (fun s => s.RIP = 0x101077) (xorR64R64Effect 0x101077 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101077 9 13).toInstrSpec (xor_r64_r64_effect_step 0x101077 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x10107a [0x4C, 0x21, 0xCB] (fun s => s.RIP = 0x10107a) (andR64R64Effect 0x10107a 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10107a 3 9).toInstrSpec (and_r64_r64_effect_step 0x10107a 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x10107d [0x48, 0x89, 0x1C, 0x24] (StorePre 0x10107d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10107d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10107d 3 (.sib 4 none 0 .none))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10107d 3 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10107d 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f100 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 239), (1, 191), (2, 235), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 129), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101047) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f101 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 239), (1, 191), (2, 235), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 241), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10104a) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f102 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 239), (1, 191), (2, 235), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 243), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10104d) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f103 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 239), (1, 191), (2, 245), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 243), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101050) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f104 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 247), (1, 191), (2, 245), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 243), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101053) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f105 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 247), (1, 249), (2, 245), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 243), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101056) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f106 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 247), (1, 251), (2, 245), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 243), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101059) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f107 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 247), (1, 251), (2, 245), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 253), (10, 207), (11, 227), (12, 243), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10105c) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f108 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 247), (1, 251), (2, 245), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 253), (10, 207), (11, 227), (12, 243), (13, 255), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10105f) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f109 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 247), (1, 251), (2, 245), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 253), (10, 207), (11, 227), (12, 243), (13, 257), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101062) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f110 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 247), (1, 251), (2, 245), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 253), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101065) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f111 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 247), (1, 251), (2, 261), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 253), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101068) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f112 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 263), (1, 251), (2, 261), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 253), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10106b) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f113 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 263), (1, 265), (2, 261), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 253), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10106e) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f114 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 263), (1, 267), (2, 261), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 253), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101071) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.out (n := 269) f115 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 270) (ρ' := [(0, 263), (1, 269), (2, 261), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 253), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101074) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.out (n := 271) f116 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 272) (ρ' := [(0, 263), (1, 269), (2, 261), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 271), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101077) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f117 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 263), (1, 269), (2, 261), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 273), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10107a) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f118 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 263), (1, 269), (2, 261), (3, 275), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 273), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10107d) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.exec (n := 277) (ρ' := [(0, 263), (1, 269), (2, 261), (3, 275), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 273), (10, 207), (11, 227), (12, 243), (13, 259), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101081) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l100eed_6 code

theorem rest_l100eed_4 [Bindings] (code : CodeMap) :
    Rest (n := 199) code lifted (codeRange 0x100eed bytes_l100eed) [(0, 197), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]
      113 0x101005 bytes_l100eed_4 b_l100eed_4 := by
  have f80 : InstrSpec 0x101005 [0x48, 0x31, 0xD8] (fun s => s.RIP = 0x101005) (xorR64R64Effect 0x101005 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101005 0 3).toInstrSpec (xor_r64_r64_effect_step 0x101005 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x101008 [0x4C, 0x31, 0xD8] (fun s => s.RIP = 0x101008) (xorR64R64Effect 0x101008 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101008 0 11).toInstrSpec (xor_r64_r64_effect_step 0x101008 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x10100b [0x49, 0x31, 0xF1] (fun s => s.RIP = 0x10100b) (xorR64R64Effect 0x10100b 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10100b 9 6).toInstrSpec (xor_r64_r64_effect_step 0x10100b 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x10100e [0x4C, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x10100e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10100e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10100e 10 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10100e 10 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10100e 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f84 : InstrSpec 0x101013 [0x4D, 0x31, 0xEA] (fun s => s.RIP = 0x101013) (xorR64R64Effect 0x101013 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101013 10 13).toInstrSpec (xor_r64_r64_effect_step 0x101013 0x4d 0xea (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x101016 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x101016) (movR64R64Effect 0x101016 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x101016 6 5).toInstrSpec (mov_r64_r64_effect_step 0x101016 0x48 0xee (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x101019 [0x4C, 0x31, 0xE6] (fun s => s.RIP = 0x101019) (xorR64R64Effect 0x101019 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101019 6 12).toInstrSpec (xor_r64_r64_effect_step 0x101019 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x10101c [0x4D, 0x89, 0xD3] (fun s => s.RIP = 0x10101c) (movR64R64Effect 0x10101c 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10101c 11 10).toInstrSpec (mov_r64_r64_effect_step 0x10101c 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x10101f [0x49, 0x21, 0xF3] (fun s => s.RIP = 0x10101f) (andR64R64Effect 0x10101f 11 6)
      [.gpr 11, .gpr 6] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10101f 11 6).toInstrSpec (and_r64_r64_effect_step 0x10101f 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x101022 [0x4D, 0x31, 0xD9] (fun s => s.RIP = 0x101022) (xorR64R64Effect 0x101022 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101022 9 11).toInstrSpec (xor_r64_r64_effect_step 0x101022 0x4d 0xd9 (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x101025 [0x48, 0x31, 0xD0] (fun s => s.RIP = 0x101025) (xorR64R64Effect 0x101025 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101025 0 2).toInstrSpec (xor_r64_r64_effect_step 0x101025 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x101028 [0x49, 0x31, 0xD1] (fun s => s.RIP = 0x101028) (xorR64R64Effect 0x101028 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101028 9 2).toInstrSpec (xor_r64_r64_effect_step 0x101028 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x10102b [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x10102b) (movR64R64Effect 0x10102b 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10102b 11 0).toInstrSpec (mov_r64_r64_effect_step 0x10102b 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x10102e [0x48, 0x8B, 0x1C, 0x24] (LoadPre 0x10102e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10102e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10102e 3 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10102e 3 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10102e 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f94 : InstrSpec 0x101032 [0x49, 0x31, 0xDB] (fun s => s.RIP = 0x101032) (xorR64R64Effect 0x101032 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101032 11 3).toInstrSpec (xor_r64_r64_effect_step 0x101032 0x49 0xdb (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x101035 [0x4D, 0x89, 0xDD] (fun s => s.RIP = 0x101035) (movR64R64Effect 0x101035 13 11)
      [.gpr 11] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x101035 13 11).toInstrSpec (mov_r64_r64_effect_step 0x101035 0x4d 0xdd (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x101038 [0x4D, 0x21, 0xCD] (fun s => s.RIP = 0x101038) (andR64R64Effect 0x101038 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101038 13 9).toInstrSpec (and_r64_r64_effect_step 0x101038 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x10103b [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x10103b) (movR64R64Effect 0x10103b 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10103b 2 13).toInstrSpec (mov_r64_r64_effect_step 0x10103b 0x4c 0xea (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x10103e [0x4C, 0x31, 0xF2] (fun s => s.RIP = 0x10103e) (xorR64R64Effect 0x10103e 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10103e 2 14).toInstrSpec (xor_r64_r64_effect_step 0x10103e 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x101041 [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x101041) (xorR64R64Effect 0x101041 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x101041 0 1).toInstrSpec (xor_r64_r64_effect_step 0x101041 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f80 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 199), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101008) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f81 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 201), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10100b) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f82 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 201), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 164), (7, 7), (8, 114), (9, 203), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10100e) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f83 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 201), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 164), (7, 7), (8, 114), (9, 203), (10, 205), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101013) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f84 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 201), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 164), (7, 7), (8, 114), (9, 203), (10, 207), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101016) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f85 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 201), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 209), (7, 7), (8, 114), (9, 203), (10, 207), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101019) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f86 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 201), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 203), (10, 207), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10101c) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f87 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(0, 201), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 203), (10, 207), (11, 213), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10101f) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f88 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 201), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 203), (10, 207), (11, 215), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101022) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f89 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 201), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 217), (10, 207), (11, 215), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101025) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f90 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 219), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 217), (10, 207), (11, 215), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101028) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f91 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 219), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 215), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10102b) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f92 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 219), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 223), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10102e) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f93 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 219), (1, 191), (2, 123), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 223), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101032) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f94 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 219), (1, 191), (2, 123), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101035) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f95 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 219), (1, 191), (2, 123), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 129), (13, 229), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101038) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f96 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 219), (1, 191), (2, 123), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 129), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10103b) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f97 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 234) (ρ' := [(0, 219), (1, 191), (2, 233), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 129), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10103e) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f98 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(0, 219), (1, 191), (2, 235), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 129), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101041) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 238) (ρ' := [(0, 237), (1, 191), (2, 235), (3, 225), (4, 4), (5, 193), (6, 211), (7, 7), (8, 114), (9, 221), (10, 207), (11, 227), (12, 129), (13, 231), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101044) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100eed_5 code

theorem rest_l100eed_3 [Bindings] (code : CodeMap) :
    Rest (n := 162) code lifted (codeRange 0x100eed bytes_l100eed) [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 153), (7, 7), (8, 114), (9, 89), (10, 160), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]
      133 0x100fbd bytes_l100eed_3 b_l100eed_3 := by
  have f60 : InstrSpec 0x100fbd [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x100fbd) (movR64R64Effect 0x100fbd 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100fbd 6 14).toInstrSpec (mov_r64_r64_effect_step 0x100fbd 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x100fc0 [0x48, 0x23, 0x74, 0x24, 0x28] (LoadPre 0x100fc0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100fc0 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x100fc0 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (andR64M64Effect_footprint 0x100fc0 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (and_r64_m64_effect_step 0x100fc0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f62 : InstrSpec 0x100fc5 [0x49, 0x89, 0xDB] (fun s => s.RIP = 0x100fc5) (movR64R64Effect 0x100fc5 11 3)
      [.gpr 3] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x100fc5 11 3).toInstrSpec (mov_r64_r64_effect_step 0x100fc5 0x49 0xdb (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x100fc8 [0x48, 0x8B, 0x5C, 0x24, 0x10] (LoadPre 0x100fc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100fc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100fc8 3 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x100fc8 3 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100fc8 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f64 : InstrSpec 0x100fcd [0x49, 0x21, 0xDB] (fun s => s.RIP = 0x100fcd) (andR64R64Effect 0x100fcd 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100fcd 11 3).toInstrSpec (and_r64_r64_effect_step 0x100fcd 0x49 0xdb (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x100fd0 [0x4C, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x100fd0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100fd0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100fd0 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x100fd0 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100fd0 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x100fd5 [0x4D, 0x31, 0xFE] (fun s => s.RIP = 0x100fd5) (xorR64R64Effect 0x100fd5 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100fd5 14 15).toInstrSpec (xor_r64_r64_effect_step 0x100fd5 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x100fd8 [0x4C, 0x89, 0x74, 0x24, 0x08] (StorePre 0x100fd8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100fd8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100fd8 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100fd8 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100fd8 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x100fdd [0x4D, 0x21, 0xEE] (fun s => s.RIP = 0x100fdd) (andR64R64Effect 0x100fdd 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100fdd 14 13).toInstrSpec (and_r64_r64_effect_step 0x100fdd 0x4d 0xee (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x100fe0 [0x4C, 0x89, 0x6C, 0x24, 0x40] (StorePre 0x100fe0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100fe0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100fe0 13 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100fe0 13 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x100fe0 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x100fe5 [0x4D, 0x31, 0xE6] (fun s => s.RIP = 0x100fe5) (xorR64R64Effect 0x100fe5 14 12)
      [.gpr 14, .gpr 12] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100fe5 14 12).toInstrSpec (xor_r64_r64_effect_step 0x100fe5 0x4d 0xe6 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x100fe8 [0x4C, 0x89, 0x64, 0x24, 0x38] (StorePre 0x100fe8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100fe8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100fe8 12 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100fe8 12 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x100fe8 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x100fed [0x49, 0x31, 0xF6] (fun s => s.RIP = 0x100fed) (xorR64R64Effect 0x100fed 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100fed 14 6).toInstrSpec (xor_r64_r64_effect_step 0x100fed 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x100ff0 [0x4D, 0x31, 0xC6] (fun s => s.RIP = 0x100ff0) (xorR64R64Effect 0x100ff0 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100ff0 14 8).toInstrSpec (xor_r64_r64_effect_step 0x100ff0 0x4d 0xc6 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x100ff3 [0x49, 0x31, 0xCE] (fun s => s.RIP = 0x100ff3) (xorR64R64Effect 0x100ff3 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100ff3 14 1).toInstrSpec (xor_r64_r64_effect_step 0x100ff3 0x49 0xce (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x100ff6 [0x4C, 0x31, 0xD9] (fun s => s.RIP = 0x100ff6) (xorR64R64Effect 0x100ff6 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100ff6 1 11).toInstrSpec (xor_r64_r64_effect_step 0x100ff6 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x100ff9 [0x4C, 0x31, 0xD1] (fun s => s.RIP = 0x100ff9) (xorR64R64Effect 0x100ff9 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100ff9 1 10).toInstrSpec (xor_r64_r64_effect_step 0x100ff9 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x100ffc [0x4C, 0x31, 0xFD] (fun s => s.RIP = 0x100ffc) (xorR64R64Effect 0x100ffc 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100ffc 5 15).toInstrSpec (xor_r64_r64_effect_step 0x100ffc 0x4c 0xfd (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x100fff [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x100fff) (movR64R64Effect 0x100fff 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100fff 0 5).toInstrSpec (mov_r64_r64_effect_step 0x100fff 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x101002 [0x4C, 0x21, 0xF8] (fun s => s.RIP = 0x101002) (andR64R64Effect 0x101002 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x101002 0 15).toInstrSpec (and_r64_r64_effect_step 0x101002 0x4c 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f60 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 162), (7, 7), (8, 114), (9, 89), (10, 160), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fc0) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f61 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fc5) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f62 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 166), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fc8) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f63 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 166), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fcd) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f64 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fd0) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f65 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 172), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fd5) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f66 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 174), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fd8) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.exec (n := 176) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 174), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fdd) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f68 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 177), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fe0) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.exec (n := 179) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 177), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fe5) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f70 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 180), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fe8) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.exec (n := 182) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 180), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fed) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f72 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 183), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ff0) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f73 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 185), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ff3) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f74 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ff6) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f75 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 61), (1, 189), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ff9) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f76 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 61), (1, 191), (2, 123), (3, 168), (4, 4), (5, 53), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ffc) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f77 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 61), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fff) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 195), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101002) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f79 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 197), (1, 191), (2, 123), (3, 168), (4, 4), (5, 193), (6, 164), (7, 7), (8, 114), (9, 89), (10, 160), (11, 170), (12, 129), (13, 133), (14, 187), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101005) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100eed_4 code

theorem rest_l100eed_2 [Bindings] (code : CodeMap) :
    Rest (n := 125) code lifted (codeRange 0x100eed bytes_l100eed) [(0, 61), (1, 93), (2, 123), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]
      153 0x100f7c bytes_l100eed_2 b_l100eed_2 := by
  have f40 : InstrSpec 0x100f7c [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x100f7c) (movR64R64Effect 0x100f7c 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x100f7c 1 8).toInstrSpec (mov_r64_r64_effect_step 0x100f7c 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x100f7f [0x4C, 0x21, 0xD1] (fun s => s.RIP = 0x100f7f) (andR64R64Effect 0x100f7f 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100f7f 1 10).toInstrSpec (and_r64_r64_effect_step 0x100f7f 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x100f82 [0x4D, 0x89, 0xD4] (fun s => s.RIP = 0x100f82) (movR64R64Effect 0x100f82 12 10)
      [.gpr 10] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x100f82 12 10).toInstrSpec (mov_r64_r64_effect_step 0x100f82 0x4d 0xd4 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x100f85 [0x48, 0x31, 0xF1] (fun s => s.RIP = 0x100f85) (xorR64R64Effect 0x100f85 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f85 1 6).toInstrSpec (xor_r64_r64_effect_step 0x100f85 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x100f88 [0x4C, 0x8B, 0x2F] (LoadPre 0x100f88 (fun s => AddrMode.addr (.base 7 .none) s (0x100f88 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100f88 13 (.base 7 .none))
      [.gpr 7] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x100f88 13 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x100f88 0x4c (by decide) 5 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f45 : InstrSpec 0x100f8b [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x100f8b) (movR64R64Effect 0x100f8b 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100f8b 6 3).toInstrSpec (mov_r64_r64_effect_step 0x100f8b 0x48 0xde (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x100f8e [0x4C, 0x31, 0xEE] (fun s => s.RIP = 0x100f8e) (xorR64R64Effect 0x100f8e 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f8e 6 13).toInstrSpec (xor_r64_r64_effect_step 0x100f8e 0x4c 0xee (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x100f91 [0x49, 0x89, 0xF3] (fun s => s.RIP = 0x100f91) (movR64R64Effect 0x100f91 11 6)
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x100f91 11 6).toInstrSpec (mov_r64_r64_effect_step 0x100f91 0x49 0xf3 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x100f94 [0x48, 0x89, 0x74, 0x24, 0x20] (StorePre 0x100f94 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100f94 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f94 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f94 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x100f94 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x100f99 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x100f99) (movR64R64Effect 0x100f99 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100f99 6 3).toInstrSpec (mov_r64_r64_effect_step 0x100f99 0x48 0xde (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x100f9c [0x4C, 0x31, 0xFE] (fun s => s.RIP = 0x100f9c) (xorR64R64Effect 0x100f9c 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f9c 6 15).toInstrSpec (xor_r64_r64_effect_step 0x100f9c 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x100f9f [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x100f9f) (movR64R64Effect 0x100f9f 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x100f9f 3 6).toInstrSpec (mov_r64_r64_effect_step 0x100f9f 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x100fa2 [0x48, 0x89, 0x34, 0x24] (StorePre 0x100fa2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100fa2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100fa2 6 (.sib 4 none 0 .none))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100fa2 6 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x100fa2 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x100fa6 [0x4D, 0x31, 0xEF] (fun s => s.RIP = 0x100fa6) (xorR64R64Effect 0x100fa6 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100fa6 15 13).toInstrSpec (xor_r64_r64_effect_step 0x100fa6 0x4d 0xef (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x100fa9 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x100fa9) (movR64R64Effect 0x100fa9 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100fa9 6 15).toInstrSpec (mov_r64_r64_effect_step 0x100fa9 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x100fac [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x100fac) (xorR64R64Effect 0x100fac 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100fac 6 0).toInstrSpec (xor_r64_r64_effect_step 0x100fac 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x100faf [0x48, 0x89, 0x74, 0x24, 0x30] (StorePre 0x100faf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100faf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100faf 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100faf 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x100faf 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x100fb4 [0x4D, 0x89, 0xDA] (fun s => s.RIP = 0x100fb4) (movR64R64Effect 0x100fb4 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x100fb4 10 11).toInstrSpec (mov_r64_r64_effect_step 0x100fb4 0x4d 0xda (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x100fb7 [0x49, 0x21, 0xF2] (fun s => s.RIP = 0x100fb7) (andR64R64Effect 0x100fb7 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100fb7 10 6).toInstrSpec (and_r64_r64_effect_step 0x100fb7 0x49 0xf2 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x100fba [0x49, 0x31, 0xC2] (fun s => s.RIP = 0x100fba) (xorR64R64Effect 0x100fba 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100fba 10 0).toInstrSpec (xor_r64_r64_effect_step 0x100fba 0x49 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 61), (1, 125), (2, 123), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f7f) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 61), (1, 127), (2, 123), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f82) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f42 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 61), (1, 127), (2, 123), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (12, 129), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f85) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (12, 129), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f88) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f44 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (12, 129), (13, 133), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f8b) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f45 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 102), (4, 4), (5, 53), (6, 135), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (12, 129), (13, 133), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f8e) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f46 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 102), (4, 4), (5, 53), (6, 137), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (12, 129), (13, 133), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f91) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f47 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 102), (4, 4), (5, 53), (6, 137), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f94) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 102), (4, 4), (5, 53), (6, 137), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f99) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f49 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 102), (4, 4), (5, 53), (6, 142), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f9c) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f50 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 102), (4, 4), (5, 53), (6, 144), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f9f) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f51 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 144), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fa2) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.exec (n := 148) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 144), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fa6) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f53 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 144), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fa9) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f54 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 151), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fac) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f55 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 153), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100faf) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.exec (n := 155) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 153), (7, 7), (8, 114), (9, 89), (10, 109), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fb4) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f57 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 153), (7, 7), (8, 114), (9, 89), (10, 156), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fb7) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f58 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 153), (7, 7), (8, 114), (9, 89), (10, 158), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fba) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f59 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 61), (1, 131), (2, 123), (3, 146), (4, 4), (5, 53), (6, 153), (7, 7), (8, 114), (9, 89), (10, 160), (11, 139), (12, 129), (13, 133), (14, 87), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100fbd) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100eed_3 code

theorem rest_l100eed_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x100eed bytes_l100eed) [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (9, 83), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      173 0x100f37 bytes_l100eed_1 b_l100eed_1 := by
  have f20 : InstrSpec 0x100f37 [0x4D, 0x31, 0xF9] (fun s => s.RIP = 0x100f37) (xorR64R64Effect 0x100f37 9 15)
      [.gpr 9, .gpr 15] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f37 9 15).toInstrSpec (xor_r64_r64_effect_step 0x100f37 0x4d 0xf9 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x100f3a [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x100f3a) (movR64R64Effect 0x100f3a 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x100f3a 1 0).toInstrSpec (mov_r64_r64_effect_step 0x100f3a 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x100f3d [0x4C, 0x31, 0xC1] (fun s => s.RIP = 0x100f3d) (xorR64R64Effect 0x100f3d 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f3d 1 8).toInstrSpec (xor_r64_r64_effect_step 0x100f3d 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x100f40 [0x48, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x100f40 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100f40 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f40 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f40 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x100f40 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x100f45 [0x4D, 0x89, 0xC8] (fun s => s.RIP = 0x100f45) (movR64R64Effect 0x100f45 8 9)
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x100f45 8 9).toInstrSpec (mov_r64_r64_effect_step 0x100f45 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x100f48 [0x49, 0x31, 0xC8] (fun s => s.RIP = 0x100f48) (xorR64R64Effect 0x100f48 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f48 8 1).toInstrSpec (xor_r64_r64_effect_step 0x100f48 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x100f4b [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x100f4b) (movR64R64Effect 0x100f4b 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100f4b 6 8).toInstrSpec (mov_r64_r64_effect_step 0x100f4b 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x100f4e [0x4C, 0x89, 0xC3] (fun s => s.RIP = 0x100f4e) (movR64R64Effect 0x100f4e 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x100f4e 3 8).toInstrSpec (mov_r64_r64_effect_step 0x100f4e 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x100f51 [0x4C, 0x89, 0x44, 0x24, 0x48] (StorePre 0x100f51 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100f51 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f51 8 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f51 8 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x100f51 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x100f56 [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x100f56) (andR64R64Effect 0x100f56 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100f56 6 1).toInstrSpec (and_r64_r64_effect_step 0x100f56 0x48 0xce (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x100f59 [0x4C, 0x33, 0x7F, 0x28] (LoadPre 0x100f59 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x100f59 + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x100f59 15 (.base 7 (.d8 0x28)))
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (xorR64M64Effect_footprint 0x100f59 15 (.base 7 (.d8 0x28))).toInstrSpec (xor_r64_m64_effect_step 0x100f59 0x4c (by decide) 7 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x100f5d [0x49, 0x31, 0xC2] (fun s => s.RIP = 0x100f5d) (xorR64R64Effect 0x100f5d 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f5d 10 0).toInstrSpec (xor_r64_r64_effect_step 0x100f5d 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x100f60 [0x4D, 0x89, 0xF0] (fun s => s.RIP = 0x100f60) (movR64R64Effect 0x100f60 8 14)
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x100f60 8 14).toInstrSpec (mov_r64_r64_effect_step 0x100f60 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x100f63 [0x4C, 0x89, 0x74, 0x24, 0x18] (StorePre 0x100f63 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100f63 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f63 14 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f63 14 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x100f63 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x100f68 [0x4D, 0x31, 0xF8] (fun s => s.RIP = 0x100f68) (xorR64R64Effect 0x100f68 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f68 8 15).toInstrSpec (xor_r64_r64_effect_step 0x100f68 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x100f6b [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x100f6b) (movR64R64Effect 0x100f6b 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100f6b 2 3).toInstrSpec (mov_r64_r64_effect_step 0x100f6b 0x48 0xda (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x100f6e [0x4C, 0x31, 0xC2] (fun s => s.RIP = 0x100f6e) (xorR64R64Effect 0x100f6e 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f6e 2 8).toInstrSpec (xor_r64_r64_effect_step 0x100f6e 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x100f71 [0x48, 0x89, 0x54, 0x24, 0x50] (StorePre 0x100f71 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100f71 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f71 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f71 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x100f71 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x100f76 [0x4C, 0x21, 0xDA] (fun s => s.RIP = 0x100f76) (andR64R64Effect 0x100f76 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x100f76 2 11).toInstrSpec (and_r64_r64_effect_step 0x100f76 0x4c 0xda (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x100f79 [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x100f79) (xorR64R64Effect 0x100f79 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f79 2 6).toInstrSpec (xor_r64_r64_effect_step 0x100f79 0x48 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f3a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 61), (1, 91), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f3d) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 61), (1, 93), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f40) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 61), (1, 93), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f45) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 61), (1, 93), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 96), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f48) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 61), (1, 93), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 98), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f4b) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f26 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 61), (1, 93), (2, 68), (4, 4), (5, 53), (6, 100), (7, 7), (8, 98), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f4e) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f27 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 61), (1, 93), (2, 68), (3, 102), (4, 4), (5, 53), (6, 100), (7, 7), (8, 98), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f51) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 61), (1, 93), (2, 68), (3, 102), (4, 4), (5, 53), (6, 100), (7, 7), (8, 98), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f56) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 61), (1, 93), (2, 68), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 98), (9, 89), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f59) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 61), (1, 93), (2, 68), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 98), (9, 89), (10, 55), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f5d) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f31 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 61), (1, 93), (2, 68), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 98), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f60) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f32 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 61), (1, 93), (2, 68), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 111), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f63) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 61), (1, 93), (2, 68), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 111), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f68) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f34 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 61), (1, 93), (2, 68), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f6b) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 61), (1, 93), (2, 116), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f6e) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 61), (1, 93), (2, 118), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f71) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.exec (n := 120) (ρ' := [(0, 61), (1, 93), (2, 118), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f76) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 61), (1, 93), (2, 121), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f79) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f39 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 61), (1, 93), (2, 123), (3, 102), (4, 4), (5, 53), (6, 105), (7, 7), (8, 114), (9, 89), (10, 109), (11, 78), (14, 87), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f7c) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100eed_2 code

theorem rest_l100eed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100eed bytes_l100eed) (entryMap (live .l100eed))
      193 0x100eed bytes_l100eed b_l100eed := by
  have f0 : InstrSpec 0x100eed [0x48, 0x8B, 0x6F, 0x08] (LoadPre 0x100eed (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100eed + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100eed 5 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x100eed 5 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x100eed 0x48 (by decide) 5 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100ef1 [0x4C, 0x8B, 0x57, 0x10] (LoadPre 0x100ef1 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x100ef1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ef1 10 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x100ef1 10 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x100ef1 0x4c (by decide) 2 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100ef5 [0x48, 0x8B, 0x77, 0x20] (LoadPre 0x100ef5 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x100ef5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ef5 6 (.base 7 (.d8 0x20)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100ef5 6 (.base 7 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x100ef5 0x48 (by decide) 6 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100ef9 [0x4C, 0x8B, 0x7F, 0x30] (LoadPre 0x100ef9 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x100ef9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ef9 15 (.base 7 (.d8 0x30)))
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x100ef9 15 (.base 7 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x100ef9 0x4c (by decide) 7 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100efd [0x48, 0x8B, 0x47, 0x38] (LoadPre 0x100efd (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x100efd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100efd 0 (.base 7 (.d8 0x38)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x100efd 0 (.base 7 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x100efd 0x48 (by decide) 0 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100f01 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x100f01) (movR64R64Effect 0x100f01 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x100f01 2 6).toInstrSpec (mov_r64_r64_effect_step 0x100f01 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100f04 [0x49, 0x89, 0xF0] (fun s => s.RIP = 0x100f04) (movR64R64Effect 0x100f04 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x100f04 8 6).toInstrSpec (mov_r64_r64_effect_step 0x100f04 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100f07 [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x100f07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f07 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f07 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f07 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100f07 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100f0c [0x4C, 0x31, 0xD2] (fun s => s.RIP = 0x100f0c) (xorR64R64Effect 0x100f0c 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f0c 2 10).toInstrSpec (xor_r64_r64_effect_step 0x100f0c 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100f0f [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x100f0f) (movR64R64Effect 0x100f0f 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100f0f 6 0).toInstrSpec (mov_r64_r64_effect_step 0x100f0f 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100f12 [0x48, 0x31, 0xEE] (fun s => s.RIP = 0x100f12) (xorR64R64Effect 0x100f12 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f12 6 5).toInstrSpec (xor_r64_r64_effect_step 0x100f12 0x48 0xee (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100f15 [0x48, 0x89, 0x74, 0x24, 0x10] (StorePre 0x100f15 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100f15 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f15 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f15 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x100f15 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x100f1a [0x48, 0x31, 0xD6] (fun s => s.RIP = 0x100f1a) (xorR64R64Effect 0x100f1a 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f1a 6 2).toInstrSpec (xor_r64_r64_effect_step 0x100f1a 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x100f1d [0x48, 0x89, 0x74, 0x24, 0x28] (StorePre 0x100f1d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100f1d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f1d 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f1d 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x100f1d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x100f22 [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x100f22) (movR64R64Effect 0x100f22 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x100f22 11 2).toInstrSpec (mov_r64_r64_effect_step 0x100f22 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x100f25 [0x48, 0x89, 0x54, 0x24, 0x58] (StorePre 0x100f25 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100f25 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100f25 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100f25 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x100f25 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x100f2a [0x4C, 0x8B, 0x4F, 0x18] (LoadPre 0x100f2a (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x100f2a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100f2a 9 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x100f2a 9 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x100f2a 0x4c (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x100f2e [0x49, 0x31, 0xF1] (fun s => s.RIP = 0x100f2e) (xorR64R64Effect 0x100f2e 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f2e 9 6).toInstrSpec (xor_r64_r64_effect_step 0x100f2e 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x100f31 [0x4D, 0x89, 0xCE] (fun s => s.RIP = 0x100f31) (movR64R64Effect 0x100f31 14 9)
      [.gpr 9] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x100f31 14 9).toInstrSpec (mov_r64_r64_effect_step 0x100f31 0x4d 0xce (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x100f34 [0x4D, 0x31, 0xD6] (fun s => s.RIP = 0x100f34) (xorR64R64Effect 0x100f34 14 10)
      [.gpr 14, .gpr 10] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x100f34 14 10).toInstrSpec (xor_r64_r64_effect_step 0x100f34 0x4d 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 53), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ef1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 53), (7, 7), (10, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ef5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 4), (5, 53), (6, 57), (7, 7), (10, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ef9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 4), (5, 53), (6, 57), (7, 7), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100efd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (4, 4), (5, 53), (6, 57), (7, 7), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f01) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (2, 63), (4, 4), (5, 53), (6, 57), (7, 7), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f04) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (2, 63), (4, 4), (5, 53), (6, 57), (7, 7), (8, 65), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f07) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (2, 63), (4, 4), (5, 53), (6, 57), (7, 7), (8, 65), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f0c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 57), (7, 7), (8, 65), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f0f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 70), (7, 7), (8, 65), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f12) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 72), (7, 7), (8, 65), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f15) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 72), (7, 7), (8, 65), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f1a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f1d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (10, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f22) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (10, 55), (11, 78), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f25) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (10, 55), (11, 78), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f2a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (9, 81), (10, 55), (11, 78), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f2e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (9, 83), (10, 55), (11, 78), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f31) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f18 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (9, 83), (10, 55), (11, 78), (14, 85), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f34) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 61), (2, 68), (4, 4), (5, 53), (6, 75), (7, 7), (8, 65), (9, 83), (10, 55), (11, 78), (14, 87), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100f37) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100eed_1 code

theorem block_l100eed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100eed :=
  Rest.liftedBlock (rest_l100eed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100eed x hx)

theorem rest_l101177 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101177 bytes_l101177) (entryMap (live .l101177))
      4 0x101177 bytes_l101177 b_l101177 := by
  have f0 : InstrSpec 0x101177 [0x31, 0xFF] (fun s => s.RIP = 0x101177) (xorR32R32Effect 0x101177 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101177 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x101177 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x101179 [0x31, 0xF6] (fun s => s.RIP = 0x101179) (xorR32R32Effect 0x101179 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101179 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x101179 0xf6 (by decide)) pre_rip
  have f2 : InstrSpec 0x10117b [0x48, 0xC7, 0xC2, 0x60, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x10117b) (movR64Imm32Effect 0x10117b 2 0x200e60)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10117b 2 0x200e60).toInstrSpec (mov_r64_imm32_effect_step 0x10117b 0x48 0xc2 (by decide) (by decide) (by decide) 0x200e60) pre_rip
  have f3 : InstrSpec 0x101182 [0xE8, 0xB0, 0x26, 0x00, 0x00] (PushPre 0x101182 5) (callEffect (fun _ => 0x103837) 0x101187)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101182 0x103837 0x101187).toInstrSpec (call_rel32_effect_step 0x101182 0x26b0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x101179) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10117b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x101182) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101177 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101177 :=
  Rest.liftedBlock (rest_l101177 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101177 x hx)

theorem rest_l101187 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101187 bytes_l101187) (entryMap (live .l101187))
      4 0x101187 bytes_l101187 b_l101187 := by
  have f0 : InstrSpec 0x101187 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101187) (movR32Imm32Effect 0x101187 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x101187 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x101187 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x10118c [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10118c) (movR32Imm32Effect 0x10118c 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10118c 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10118c 0xbe (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x101191 [0x48, 0xC7, 0xC2, 0x78, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x101191) (movR64Imm32Effect 0x101191 2 0x200e78)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x101191 2 0x200e78).toInstrSpec (mov_r64_imm32_effect_step 0x101191 0x48 0xc2 (by decide) (by decide) (by decide) 0x200e78) pre_rip
  have f3 : InstrSpec 0x101198 [0xE8, 0x9A, 0x26, 0x00, 0x00] (PushPre 0x101198 5) (callEffect (fun _ => 0x103837) 0x10119d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101198 0x103837 0x10119d).toInstrSpec (call_rel32_effect_step 0x101198 0x269a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10118c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x101191) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x101198) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101187 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101187 :=
  Rest.liftedBlock (rest_l101187 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101187 x hx)

theorem rest_l10119d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10119d bytes_l10119d) (entryMap (live .l10119d))
      4 0x10119d bytes_l10119d b_l10119d := by
  have f0 : InstrSpec 0x10119d [0xBF, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10119d) (movR32Imm32Effect 0x10119d 5 7 0x2)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10119d 5 7 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x10119d 0xbf (by decide) 0x2) pre_rip
  have f1 : InstrSpec 0x1011a2 [0xBE, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1011a2) (movR32Imm32Effect 0x1011a2 5 6 0x2)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1011a2 5 6 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x1011a2 0xbe (by decide) 0x2) pre_rip
  have f2 : InstrSpec 0x1011a7 [0x48, 0xC7, 0xC2, 0x90, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x1011a7) (movR64Imm32Effect 0x1011a7 2 0x200e90)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1011a7 2 0x200e90).toInstrSpec (mov_r64_imm32_effect_step 0x1011a7 0x48 0xc2 (by decide) (by decide) (by decide) 0x200e90) pre_rip
  have f3 : InstrSpec 0x1011ae [0xE8, 0x84, 0x26, 0x00, 0x00] (PushPre 0x1011ae 5) (callEffect (fun _ => 0x103837) 0x1011b3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1011ae 0x103837 0x1011b3).toInstrSpec (call_rel32_effect_step 0x1011ae 0x2684 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x1011a2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x1011a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x1011ae) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10119d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10119d :=
  Rest.liftedBlock (rest_l10119d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10119d x hx)

theorem rest_l1011b3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1011b3 bytes_l1011b3) (entryMap (live .l1011b3))
      4 0x1011b3 bytes_l1011b3 b_l1011b3 := by
  have f0 : InstrSpec 0x1011b3 [0xBF, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1011b3) (movR32Imm32Effect 0x1011b3 5 7 0x3)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x1011b3 5 7 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x1011b3 0xbf (by decide) 0x3) pre_rip
  have f1 : InstrSpec 0x1011b8 [0xBE, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1011b8) (movR32Imm32Effect 0x1011b8 5 6 0x3)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1011b8 5 6 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x1011b8 0xbe (by decide) 0x3) pre_rip
  have f2 : InstrSpec 0x1011bd [0x48, 0xC7, 0xC2, 0xA8, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x1011bd) (movR64Imm32Effect 0x1011bd 2 0x200ea8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1011bd 2 0x200ea8).toInstrSpec (mov_r64_imm32_effect_step 0x1011bd 0x48 0xc2 (by decide) (by decide) (by decide) 0x200ea8) pre_rip
  have f3 : InstrSpec 0x1011c4 [0xE8, 0x6E, 0x26, 0x00, 0x00] (PushPre 0x1011c4 5) (callEffect (fun _ => 0x103837) 0x1011c9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1011c4 0x103837 0x1011c9).toInstrSpec (call_rel32_effect_step 0x1011c4 0x266e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x1011b8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x1011bd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x1011c4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1011b3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1011b3 :=
  Rest.liftedBlock (rest_l1011b3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1011b3 x hx)

theorem rest_l1011c9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1011c9 bytes_l1011c9) (entryMap (live .l1011c9))
      4 0x1011c9 bytes_l1011c9 b_l1011c9 := by
  have f0 : InstrSpec 0x1011c9 [0xBF, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1011c9) (movR32Imm32Effect 0x1011c9 5 7 0x4)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x1011c9 5 7 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x1011c9 0xbf (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x1011ce [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1011ce) (movR32Imm32Effect 0x1011ce 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1011ce 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x1011ce 0xbe (by decide) 0x4) pre_rip
  have f2 : InstrSpec 0x1011d3 [0x48, 0xC7, 0xC2, 0xC0, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x1011d3) (movR64Imm32Effect 0x1011d3 2 0x200ec0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1011d3 2 0x200ec0).toInstrSpec (mov_r64_imm32_effect_step 0x1011d3 0x48 0xc2 (by decide) (by decide) (by decide) 0x200ec0) pre_rip
  have f3 : InstrSpec 0x1011da [0xE8, 0x58, 0x26, 0x00, 0x00] (PushPre 0x1011da 5) (callEffect (fun _ => 0x103837) 0x1011df)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1011da 0x103837 0x1011df).toInstrSpec (call_rel32_effect_step 0x1011da 0x2658 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x1011ce) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x1011d3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x1011da) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1011c9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1011c9 :=
  Rest.liftedBlock (rest_l1011c9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1011c9 x hx)

theorem rest_l1011df [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1011df bytes_l1011df) (entryMap (live .l1011df))
      4 0x1011df bytes_l1011df b_l1011df := by
  have f0 : InstrSpec 0x1011df [0xBF, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1011df) (movR32Imm32Effect 0x1011df 5 7 0x5)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x1011df 5 7 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x1011df 0xbf (by decide) 0x5) pre_rip
  have f1 : InstrSpec 0x1011e4 [0xBE, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1011e4) (movR32Imm32Effect 0x1011e4 5 6 0x5)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1011e4 5 6 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x1011e4 0xbe (by decide) 0x5) pre_rip
  have f2 : InstrSpec 0x1011e9 [0x48, 0xC7, 0xC2, 0xD8, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x1011e9) (movR64Imm32Effect 0x1011e9 2 0x200ed8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1011e9 2 0x200ed8).toInstrSpec (mov_r64_imm32_effect_step 0x1011e9 0x48 0xc2 (by decide) (by decide) (by decide) 0x200ed8) pre_rip
  have f3 : InstrSpec 0x1011f0 [0xE8, 0x42, 0x26, 0x00, 0x00] (PushPre 0x1011f0 5) (callEffect (fun _ => 0x103837) 0x1011f5)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1011f0 0x103837 0x1011f5).toInstrSpec (call_rel32_effect_step 0x1011f0 0x2642 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x1011e4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x1011e9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x1011f0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1011df [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1011df :=
  Rest.liftedBlock (rest_l1011df code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1011df x hx)

theorem rest_l1011f5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1011f5 bytes_l1011f5) (entryMap (live .l1011f5))
      4 0x1011f5 bytes_l1011f5 b_l1011f5 := by
  have f0 : InstrSpec 0x1011f5 [0xBF, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1011f5) (movR32Imm32Effect 0x1011f5 5 7 0x6)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x1011f5 5 7 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x1011f5 0xbf (by decide) 0x6) pre_rip
  have f1 : InstrSpec 0x1011fa [0xBE, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1011fa) (movR32Imm32Effect 0x1011fa 5 6 0x6)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1011fa 5 6 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x1011fa 0xbe (by decide) 0x6) pre_rip
  have f2 : InstrSpec 0x1011ff [0x48, 0xC7, 0xC2, 0xF0, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x1011ff) (movR64Imm32Effect 0x1011ff 2 0x200ef0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1011ff 2 0x200ef0).toInstrSpec (mov_r64_imm32_effect_step 0x1011ff 0x48 0xc2 (by decide) (by decide) (by decide) 0x200ef0) pre_rip
  have f3 : InstrSpec 0x101206 [0xE8, 0x2C, 0x26, 0x00, 0x00] (PushPre 0x101206 5) (callEffect (fun _ => 0x103837) 0x10120b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101206 0x103837 0x10120b).toInstrSpec (call_rel32_effect_step 0x101206 0x262c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x1011fa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x1011ff) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x101206) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1011f5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1011f5 :=
  Rest.liftedBlock (rest_l1011f5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1011f5 x hx)

theorem rest_l10120b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10120b bytes_l10120b) (entryMap (live .l10120b))
      4 0x10120b bytes_l10120b b_l10120b := by
  have f0 : InstrSpec 0x10120b [0xBF, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10120b) (movR32Imm32Effect 0x10120b 5 7 0x7)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10120b 5 7 0x7).toInstrSpec (mov_r32_imm32_effect_step 0x10120b 0xbf (by decide) 0x7) pre_rip
  have f1 : InstrSpec 0x101210 [0xBE, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101210) (movR32Imm32Effect 0x101210 5 6 0x7)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x101210 5 6 0x7).toInstrSpec (mov_r32_imm32_effect_step 0x101210 0xbe (by decide) 0x7) pre_rip
  have f2 : InstrSpec 0x101215 [0x48, 0xC7, 0xC2, 0x08, 0x0F, 0x20, 0x00] (fun s => s.RIP = 0x101215) (movR64Imm32Effect 0x101215 2 0x200f08)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x101215 2 0x200f08).toInstrSpec (mov_r64_imm32_effect_step 0x101215 0x48 0xc2 (by decide) (by decide) (by decide) 0x200f08) pre_rip
  have f3 : InstrSpec 0x10121c [0xE8, 0x16, 0x26, 0x00, 0x00] (PushPre 0x10121c 5) (callEffect (fun _ => 0x103837) 0x101221)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10121c 0x103837 0x101221).toInstrSpec (call_rel32_effect_step 0x10121c 0x2616 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x101210) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x101215) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10121c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10120b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10120b :=
  Rest.liftedBlock (rest_l10120b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10120b x hx)

theorem rest_l101221 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101221 bytes_l101221) (entryMap (live .l101221))
      2 0x101221 bytes_l101221 b_l101221 := by
  have f0 : InstrSpec 0x101221 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101221) (fun _ => nopEffect 0x101221 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x101221 10).toInstrSpec (nop_m_effect_step 0x101221 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10122b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x10122b) (fun _ => nopEffect 0x10122b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10122b 5).toInstrSpec (nop_m_effect_step 0x10122b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x10122b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := []) (p' := 0x101230) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l101221 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101221 :=
  Rest.liftedBlock (rest_l101221 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101221 x hx)

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

theorem_by block_l100e90_eval :
    program.runBlock (dialect code) ⟨.l100e90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ea7_eval :
    program.runBlock (dialect code) ⟨.l100ea7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100eb1_eval :
    program.runBlock (dialect code) ⟨.l100eb1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ebb_eval :
    program.runBlock (dialect code) ⟨.l100ebb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ec5_eval :
    program.runBlock (dialect code) ⟨.l100ec5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ecf_eval :
    program.runBlock (dialect code) ⟨.l100ecf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ed9_eval :
    program.runBlock (dialect code) ⟨.l100ed9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100ee3_eval :
    program.runBlock (dialect code) ⟨.l100ee3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100eed_eval :
    program.runBlock (dialect code) ⟨.l100eed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101177_eval :
    program.runBlock (dialect code) ⟨.l101177, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101187_eval :
    program.runBlock (dialect code) ⟨.l101187, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10119d_eval :
    program.runBlock (dialect code) ⟨.l10119d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1011b3_eval :
    program.runBlock (dialect code) ⟨.l1011b3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1011c9_eval :
    program.runBlock (dialect code) ⟨.l1011c9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1011df_eval :
    program.runBlock (dialect code) ⟨.l1011df, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1011f5_eval :
    program.runBlock (dialect code) ⟨.l1011f5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10120b_eval :
    program.runBlock (dialect code) ⟨.l10120b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101221_eval :
    program.runBlock (dialect code) ⟨.l101221, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
