import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l100b10 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b10 bytes_l100b10) (entryMap (live .l100b10))
      9 0x100b10 bytes_l100b10 b_l100b10 := by
  have f0 : InstrSpec 0x100b10 [0x55] (PushPre 0x100b10 1) (pushR64Effect 0x100b10 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100b10 1 5).toInstrSpec (push_r64_effect_step 0x100b10 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x100b11 [0x41, 0x57] (PushPre 0x100b11 2) (pushR64Effect 0x100b11 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100b11 2 15).toInstrSpec (push_r64_rex_effect_step 0x100b11 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100b13 [0x41, 0x56] (PushPre 0x100b13 2) (pushR64Effect 0x100b13 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100b13 2 14).toInstrSpec (push_r64_rex_effect_step 0x100b13 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100b15 [0x41, 0x55] (PushPre 0x100b15 2) (pushR64Effect 0x100b15 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100b15 2 13).toInstrSpec (push_r64_rex_effect_step 0x100b15 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100b17 [0x41, 0x54] (PushPre 0x100b17 2) (pushR64Effect 0x100b17 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100b17 2 12).toInstrSpec (push_r64_rex_effect_step 0x100b17 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100b19 [0x53] (PushPre 0x100b19 1) (pushR64Effect 0x100b19 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100b19 1 3).toInstrSpec (push_r64_effect_step 0x100b19 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x100b1a [0x48, 0x83, 0xEC, 0x38] (fun s => s.RIP = 0x100b1a) (subR64Imm8Effect 0x100b1a 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x100b1a 4 0x38).toInstrSpec (sub_r64_imm8_effect_step 0x100b1a 0x48 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100b1e [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x100b1e) (testR64R64Effect 0x100b1e 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x100b1e 6 6).toInstrSpec (test_r64_r64_effect_step 0x100b1e 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b11) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b13) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b15) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b17) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b19) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b1a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b1e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b21) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel32_effect_step 0x100b21 4 0x2bf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b10 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b10 :=
  Rest.liftedBlock (rest_l100b10 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b10 x hx)

theorem rest_l100b27 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b27 bytes_l100b27) (entryMap (live .l100b27))
      2 0x100b27 bytes_l100b27 b_l100b27 := by
  have f0 : InstrSpec 0x100b27 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x100b27) (cmpR64Imm8Effect 0x100b27 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100b27 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x100b27 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b2b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100b2b 4 0x2c5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b27 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b27 :=
  Rest.liftedBlock (rest_l100b27 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b27 x hx)

theorem rest_l100b31 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b31 bytes_l100b31) (entryMap (live .l100b31))
      2 0x100b31 bytes_l100b31 b_l100b31 := by
  have f0 : InstrSpec 0x100b31 [0x48, 0x83, 0xFE, 0x02] (fun s => s.RIP = 0x100b31) (cmpR64Imm8Effect 0x100b31 6 0x2)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100b31 6 0x2).toInstrSpec (cmp_r64_imm8_effect_step 0x100b31 0x48 0xfe 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b35) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x100b35 6 0x2d1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b31 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b31 :=
  Rest.liftedBlock (rest_l100b31 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b31 x hx)

theorem rest_l100b3b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b3b bytes_l100b3b) (entryMap (live .l100b3b))
      2 0x100b3b bytes_l100b3b b_l100b3b := by
  have f0 : InstrSpec 0x100b3b [0x48, 0x83, 0xFE, 0x03] (fun s => s.RIP = 0x100b3b) (cmpR64Imm8Effect 0x100b3b 6 0x3)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100b3b 6 0x3).toInstrSpec (cmp_r64_imm8_effect_step 0x100b3b 0x48 0xfe 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b3f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100b3f 4 0x2dd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b3b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b3b :=
  Rest.liftedBlock (rest_l100b3b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b3b x hx)

theorem rest_l100b45 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b45 bytes_l100b45) (entryMap (live .l100b45))
      2 0x100b45 bytes_l100b45 b_l100b45 := by
  have f0 : InstrSpec 0x100b45 [0x48, 0x83, 0xFE, 0x04] (fun s => s.RIP = 0x100b45) (cmpR64Imm8Effect 0x100b45 6 0x4)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100b45 6 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x100b45 0x48 0xfe 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b49) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x100b49 6 0x2e9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b45 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b45 :=
  Rest.liftedBlock (rest_l100b45 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b45 x hx)

theorem rest_l100b4f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b4f bytes_l100b4f) (entryMap (live .l100b4f))
      2 0x100b4f bytes_l100b4f b_l100b4f := by
  have f0 : InstrSpec 0x100b4f [0x48, 0x83, 0xFE, 0x05] (fun s => s.RIP = 0x100b4f) (cmpR64Imm8Effect 0x100b4f 6 0x5)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100b4f 6 0x5).toInstrSpec (cmp_r64_imm8_effect_step 0x100b4f 0x48 0xfe 0x5 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100b53 4 0x2f5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b4f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b4f :=
  Rest.liftedBlock (rest_l100b4f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b4f x hx)

theorem rest_l100b59 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b59 bytes_l100b59) (entryMap (live .l100b59))
      2 0x100b59 bytes_l100b59 b_l100b59 := by
  have f0 : InstrSpec 0x100b59 [0x48, 0x83, 0xFE, 0x06] (fun s => s.RIP = 0x100b59) (cmpR64Imm8Effect 0x100b59 6 0x6)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100b59 6 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x100b59 0x48 0xfe 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b5d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x100b5d 6 0x301) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b59 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b59 :=
  Rest.liftedBlock (rest_l100b59 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b59 x hx)

theorem rest_l100b63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b63 bytes_l100b63) (entryMap (live .l100b63))
      2 0x100b63 bytes_l100b63 b_l100b63 := by
  have f0 : InstrSpec 0x100b63 [0x48, 0x83, 0xFE, 0x07] (fun s => s.RIP = 0x100b63) (cmpR64Imm8Effect 0x100b63 6 0x7)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x100b63 6 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x100b63 0x48 0xfe 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b67) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x100b67 4 0x30d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100b63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b63 :=
  Rest.liftedBlock (rest_l100b63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b63 x hx)

theorem rest_l100b6d_9 [Bindings] (code : CodeMap) :
    Rest (n := 393) code lifted (codeRange 0x100b6d bytes_l100b6d) [(0, 383), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]
      20 0x100da9 bytes_l100b6d_9 b_l100b6d_9 := by
  have f180 : InstrSpec 0x100da9 [0x66, 0x44, 0x89, 0x53, 0x04] (StorePre 0x100da9 5 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x100da9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100da9 5 10 (.base 3 (.d8 0x4)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x100da9 5 10 (.base 3 (.d8 0x4))).toInstrSpec (mov_m16_r16_rex_effect_step 0x100da9 0x44 (by decide) 2 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f181 : InstrSpec 0x100dae [0x41, 0x31, 0xD4] (fun s => s.RIP = 0x100dae) (xorR32R32Effect 0x100dae 3 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100dae 3 12 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x100dae 0x41 0xd4 (by decide) (by decide)) pre_rip
  have f182 : InstrSpec 0x100db1 [0x44, 0x31, 0xE1] (fun s => s.RIP = 0x100db1) (xorR32R32Effect 0x100db1 3 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100db1 3 1 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100db1 0x44 0xe1 (by decide) (by decide)) pre_rip
  have f183 : InstrSpec 0x100db4 [0x66, 0x89, 0x4B, 0x06] (StorePre 0x100db4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x6)) s (0x100db4 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100db4 4 1 (.base 3 (.d8 0x6)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x100db4 4 1 (.base 3 (.d8 0x6))).toInstrSpec (mov_m16_r16_effect_step 0x100db4 1 (.base 3 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f184 : InstrSpec 0x100db8 [0x44, 0x31, 0xF2] (fun s => s.RIP = 0x100db8) (xorR32R32Effect 0x100db8 3 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100db8 3 2 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x100db8 0x44 0xf2 (by decide) (by decide)) pre_rip
  have f185 : InstrSpec 0x100dbb [0x66, 0x44, 0x89, 0x63, 0x08] (StorePre 0x100dbb 5 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100dbb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100dbb 5 12 (.base 3 (.d8 0x8)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x100dbb 5 12 (.base 3 (.d8 0x8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x100dbb 0x44 (by decide) 4 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f186 : InstrSpec 0x100dc0 [0x45, 0x31, 0xF4] (fun s => s.RIP = 0x100dc0) (xorR32R32Effect 0x100dc0 3 12 14)
      [.gpr 12, .gpr 14] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100dc0 3 12 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x100dc0 0x45 0xf4 (by decide) (by decide)) pre_rip
  have f187 : InstrSpec 0x100dc3 [0x45, 0x31, 0xF5] (fun s => s.RIP = 0x100dc3) (xorR32R32Effect 0x100dc3 3 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100dc3 3 13 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x100dc3 0x45 0xf5 (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x100dc6 [0x41, 0x31, 0xC5] (fun s => s.RIP = 0x100dc6) (xorR32R32Effect 0x100dc6 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100dc6 3 13 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x100dc6 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f189 : InstrSpec 0x100dc9 [0x66, 0x44, 0x89, 0x6B, 0x0A] (StorePre 0x100dc9 5 (fun s => AddrMode.addr (.base 3 (.d8 0xa)) s (0x100dc9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100dc9 5 13 (.base 3 (.d8 0xa)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x100dc9 5 13 (.base 3 (.d8 0xa))).toInstrSpec (mov_m16_r16_rex_effect_step 0x100dc9 0x44 (by decide) 5 (.base 3 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f190 : InstrSpec 0x100dce [0x66, 0x44, 0x89, 0x63, 0x0C] (StorePre 0x100dce 5 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x100dce + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100dce 5 12 (.base 3 (.d8 0xc)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x100dce 5 12 (.base 3 (.d8 0xc))).toInstrSpec (mov_m16_r16_rex_effect_step 0x100dce 0x44 (by decide) 4 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f191 : InstrSpec 0x100dd3 [0x66, 0x89, 0x53, 0x0E] (StorePre 0x100dd3 4 (fun s => AddrMode.addr (.base 3 (.d8 0xe)) s (0x100dd3 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x100dd3 4 2 (.base 3 (.d8 0xe)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x100dd3 4 2 (.base 3 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x100dd3 2 (.base 3 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f192 : InstrSpec 0x100dd7 [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x100dd7) (addR64Imm8Effect 0x100dd7 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x100dd7 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x100dd7 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f193 : InstrSpec 0x100ddb [0x5B] (PopPre 0x100ddb) (popR64Effect 0x100ddb 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100ddb 1 3).toInstrSpec (pop_r64_effect_step 0x100ddb 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f194 : InstrSpec 0x100ddc [0x41, 0x5C] (PopPre 0x100ddc) (popR64Effect 0x100ddc 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100ddc 2 12).toInstrSpec (pop_r64_rex_effect_step 0x100ddc 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f195 : InstrSpec 0x100dde [0x41, 0x5D] (PopPre 0x100dde) (popR64Effect 0x100dde 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100dde 2 13).toInstrSpec (pop_r64_rex_effect_step 0x100dde 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f196 : InstrSpec 0x100de0 [0x41, 0x5E] (PopPre 0x100de0) (popR64Effect 0x100de0 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100de0 2 14).toInstrSpec (pop_r64_rex_effect_step 0x100de0 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f197 : InstrSpec 0x100de2 [0x41, 0x5F] (PopPre 0x100de2) (popR64Effect 0x100de2 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100de2 2 15).toInstrSpec (pop_r64_rex_effect_step 0x100de2 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f198 : InstrSpec 0x100de4 [0x5D] (PopPre 0x100de4) (popR64Effect 0x100de4 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100de4 1 5).toInstrSpec (pop_r64_effect_step 0x100de4 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f199 : InstrSpec 0x100de5 [0xC3] (RetPre 0x100de5) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x100de5).toInstrSpec (ret_effect_step 0x100de5) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 393) (RestInside.exec (n := 393) (ρ' := [(0, 383), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dae) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 394) (RestInside.out (n := 394) f181 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 395) (ρ' := [(0, 383), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 394), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db1) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 396) (RestInside.out (n := 396) f182 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 397) (ρ' := [(0, 383), (1, 396), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 394), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db4) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 398) (RestInside.exec (n := 398) (ρ' := [(0, 383), (1, 396), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 394), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100db8) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 399) (RestInside.out (n := 399) f184 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 400) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 394), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dbb) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 401) (RestInside.exec (n := 401) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 394), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc0) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 402) (RestInside.out (n := 402) f186 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 403) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 402), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc3) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 404) (RestInside.out (n := 404) f187 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 405) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 402), (13, 404), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc6) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 406) (RestInside.out (n := 406) f188 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 407) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 402), (13, 406), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dc9) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 408) (RestInside.exec (n := 408) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 402), (13, 406), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dce) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 409) (RestInside.exec (n := 409) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 402), (13, 406), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dd3) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 410) (RestInside.exec (n := 410) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 402), (13, 406), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dd7) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 411) (RestInside.out (n := 411) f192 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 412) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 53), (4, 411), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 402), (13, 406), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ddb) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 413) (RestInside.out (n := 413) f193 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 414) f193 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 415) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 413), (4, 414), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 402), (13, 406), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ddc) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f194 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 417) f194 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 418) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 413), (4, 417), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 416), (13, 406), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100dde) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 419) (RestInside.out (n := 419) f195 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 420) f195 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 421) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 413), (4, 420), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 416), (13, 419), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100de0) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 422) (RestInside.out (n := 422) f196 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 423) f196 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 424) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 413), (4, 423), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 416), (13, 419), (14, 422), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100de2) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f197 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 426) f197 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 427) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 413), (4, 426), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 416), (13, 419), (14, 422), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100de4) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f198 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 429) f198 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 430) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 413), (4, 429), (5, 428), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 416), (13, 419), (14, 422), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100de5) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 431) (RestInside.out (n := 431) f199 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 432) f199 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 433) (ρ' := [(0, 383), (1, 396), (2, 399), (3, 413), (4, 432), (5, 428), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 416), (13, 419), (14, 422), (15, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) f199 (by decide) rfl rfl rfl (by decide)

theorem rest_l100b6d_8 [Bindings] (code : CodeMap) :
    Rest (n := 355) code lifted (codeRange 0x100b6d bytes_l100b6d) [(0, 351), (1, 274), (2, 353), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 349), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]
      40 0x100d6a bytes_l100b6d_8 b_l100b6d_8 := by
  have f160 : InstrSpec 0x100d6a [0x41, 0x31, 0xD2] (fun s => s.RIP = 0x100d6a) (xorR32R32Effect 0x100d6a 3 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d6a 3 10 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d6a 0x41 0xd2 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x100d6d [0x31, 0xF2] (fun s => s.RIP = 0x100d6d) (xorR32R32Effect 0x100d6d 2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d6d 2 2 6).toInstrSpec (xor_r32_r32_effect_step 0x100d6d 0xf2 (by decide)) pre_rip
  have f162 : InstrSpec 0x100d6f [0x23, 0x4C, 0x24, 0x24] (LoadPre 0x100d6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100d6f + BitVec.ofNat 64 4)) 4) (andR32M32Effect 0x100d6f 4 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (andR32M32Effect_footprint 0x100d6f 4 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (and_r32_m32_effect_step 0x100d6f 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f163 : InstrSpec 0x100d73 [0x44, 0x31, 0xD9] (fun s => s.RIP = 0x100d73) (xorR32R32Effect 0x100d73 3 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d73 3 1 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d73 0x44 0xd9 (by decide) (by decide)) pre_rip
  have f164 : InstrSpec 0x100d76 [0x41, 0x31, 0xEE] (fun s => s.RIP = 0x100d76) (xorR32R32Effect 0x100d76 3 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d76 3 14 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d76 0x41 0xee (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x100d79 [0x41, 0x31, 0xC8] (fun s => s.RIP = 0x100d79) (xorR32R32Effect 0x100d79 3 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d79 3 8 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d79 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f166 : InstrSpec 0x100d7c [0x45, 0x31, 0xC8] (fun s => s.RIP = 0x100d7c) (xorR32R32Effect 0x100d7c 3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d7c 3 8 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d7c 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f167 : InstrSpec 0x100d7f [0x41, 0x31, 0xE8] (fun s => s.RIP = 0x100d7f) (xorR32R32Effect 0x100d7f 3 8 5)
      [.gpr 8, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d7f 3 8 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d7f 0x41 0xe8 (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x100d82 [0x44, 0x33, 0x2C, 0x24] (LoadPre 0x100d82 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100d82 + BitVec.ofNat 64 4)) 4) (xorR32M32Effect 0x100d82 13 (.sib 4 none 0 .none))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (xorR32M32Effect_footprint 0x100d82 13 (.sib 4 none 0 .none)).toInstrSpec (xor_r32_m32_effect_step 0x100d82 0x44 (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f169 : InstrSpec 0x100d86 [0x33, 0x4C, 0x24, 0x0C] (LoadPre 0x100d86 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100d86 + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x100d86 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (xorR32M32LowEffect_footprint 0x100d86 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (xor_r32_m32_low_effect_step 0x100d86 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f170 : InstrSpec 0x100d8a [0x44, 0x31, 0xF9] (fun s => s.RIP = 0x100d8a) (xorR32R32Effect 0x100d8a 3 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d8a 3 1 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d8a 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x100d8d [0x31, 0xCF] (fun s => s.RIP = 0x100d8d) (xorR32R32Effect 0x100d8d 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d8d 2 7 1).toInstrSpec (xor_r32_r32_effect_step 0x100d8d 0xcf (by decide)) pre_rip
  have f172 : InstrSpec 0x100d8f [0x31, 0xC7] (fun s => s.RIP = 0x100d8f) (xorR32R32Effect 0x100d8f 2 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d8f 2 7 0).toInstrSpec (xor_r32_r32_effect_step 0x100d8f 0xc7 (by decide)) pre_rip
  have f173 : InstrSpec 0x100d91 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x100d91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100d91 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100d91 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100d91 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x100d91 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f174 : InstrSpec 0x100d95 [0x44, 0x31, 0xC0] (fun s => s.RIP = 0x100d95) (xorR32R32Effect 0x100d95 3 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d95 3 0 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d95 0x44 0xc0 (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x100d98 [0x41, 0x31, 0xF8] (fun s => s.RIP = 0x100d98) (xorR32R32Effect 0x100d98 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d98 3 8 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d98 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f176 : InstrSpec 0x100d9b [0x44, 0x31, 0xCF] (fun s => s.RIP = 0x100d9b) (xorR32R32Effect 0x100d9b 3 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d9b 3 7 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d9b 0x44 0xcf (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x100d9e [0x66, 0x89, 0x3B] (StorePre 0x100d9e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x100d9e + BitVec.ofNat 64 3)) 2) (movM16R16Effect 0x100d9e 3 7 (.base 3 .none))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x100d9e 3 7 (.base 3 .none)).toInstrSpec (mov_m16_r16_effect_step 0x100d9e 7 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f178 : InstrSpec 0x100da1 [0x66, 0x44, 0x89, 0x43, 0x02] (StorePre 0x100da1 5 (fun s => AddrMode.addr (.base 3 (.d8 0x2)) s (0x100da1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100da1 5 8 (.base 3 (.d8 0x2)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x100da1 5 8 (.base 3 (.d8 0x2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x100da1 0x44 (by decide) 0 (.base 3 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f179 : InstrSpec 0x100da6 [0x41, 0x31, 0xC2] (fun s => s.RIP = 0x100da6) (xorR32R32Effect 0x100da6 3 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100da6 3 10 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x100da6 0x41 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f160 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 351), (1, 274), (2, 353), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 355), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d6d) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f161 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 351), (1, 274), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 355), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d6f) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f162 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 351), (1, 359), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 355), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d73) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f163 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 351), (1, 361), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 355), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d76) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 363) (RestInside.out (n := 363) f164 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 364) (ρ' := [(0, 351), (1, 361), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 355), (11, 296), (12, 325), (13, 345), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d79) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f165 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 351), (1, 361), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 365), (9, 290), (10, 355), (11, 296), (12, 325), (13, 345), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d7c) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f166 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 351), (1, 361), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 367), (9, 290), (10, 355), (11, 296), (12, 325), (13, 345), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d7f) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f167 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 370) (ρ' := [(0, 351), (1, 361), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 369), (9, 290), (10, 355), (11, 296), (12, 325), (13, 345), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d82) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f168 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 351), (1, 361), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 369), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d86) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f169 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 374) (ρ' := [(0, 351), (1, 373), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 369), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d8a) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 375) (RestInside.out (n := 375) f170 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 376) (ρ' := [(0, 351), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 369), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d8d) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 377) (RestInside.out (n := 377) f171 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 378) (ρ' := [(0, 351), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 377), (8, 369), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d8f) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 379) (RestInside.out (n := 379) f172 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 380) (ρ' := [(0, 351), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 379), (8, 369), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d91) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 381) (RestInside.out (n := 381) f173 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 382) (ρ' := [(0, 381), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 379), (8, 369), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d95) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 383) (RestInside.out (n := 383) f174 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 384) (ρ' := [(0, 383), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 379), (8, 369), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d98) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 385) (RestInside.out (n := 385) f175 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 386) (ρ' := [(0, 383), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 379), (8, 385), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d9b) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 387) (RestInside.out (n := 387) f176 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 388) (ρ' := [(0, 383), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d9e) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 389) (RestInside.exec (n := 389) (ρ' := [(0, 383), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100da1) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 390) (RestInside.exec (n := 390) (ρ' := [(0, 383), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 355), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100da6) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f179 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 392) (ρ' := [(0, 383), (1, 375), (2, 357), (3, 53), (4, 4), (5, 337), (6, 300), (7, 387), (8, 385), (9, 290), (10, 391), (11, 296), (12, 325), (13, 371), (14, 363), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100da9) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100b6d_9 code

theorem rest_l100b6d_7 [Bindings] (code : CodeMap) :
    Rest (n := 316) code lifted (codeRange 0x100b6d bytes_l100b6d) [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 304), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 312), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]
      60 0x100d26 bytes_l100b6d_7 b_l100b6d_7 := by
  have f140 : InstrSpec 0x100d26 [0x44, 0x31, 0xF5] (fun s => s.RIP = 0x100d26) (xorR32R32Effect 0x100d26 3 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d26 3 5 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d26 0x44 0xf5 (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x100d29 [0x45, 0x89, 0xF7] (fun s => s.RIP = 0x100d29) (movR32R32Effect 0x100d29 3 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x100d29 3 15 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x100d29 0x45 0xf7 (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x100d2c [0x41, 0x21, 0xC0] (fun s => s.RIP = 0x100d2c) (andR32R32Effect 0x100d2c 3 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100d2c 3 8 0).toInstrSpec (and_r32_r32_rex_effect_step 0x100d2c 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x100d2f [0x21, 0x04, 0x24] (StorePre 0x100d2f 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100d2f + BitVec.ofNat 64 3)) 4) (andMREffect 0x100d2f 3 32 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (andMREffect32_footprint 0x100d2f 3 0 (.sib 4 none 0 .none)).toInstrSpec (and_m32_r32_effect_step 0x100d2f 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f144 : InstrSpec 0x100d32 [0x45, 0x31, 0xDC] (fun s => s.RIP = 0x100d32) (xorR32R32Effect 0x100d32 3 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d32 3 12 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d32 0x45 0xdc (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x100d35 [0x41, 0x31, 0xEC] (fun s => s.RIP = 0x100d35) (xorR32R32Effect 0x100d35 3 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d35 3 12 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d35 0x41 0xec (by decide) (by decide)) pre_rip
  have f146 : InstrSpec 0x100d38 [0x41, 0x31, 0xCD] (fun s => s.RIP = 0x100d38) (xorR32R32Effect 0x100d38 3 13 1)
      [.gpr 13, .gpr 1] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d38 3 13 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d38 0x41 0xcd (by decide) (by decide)) pre_rip
  have f147 : InstrSpec 0x100d3b [0x44, 0x31, 0xE8] (fun s => s.RIP = 0x100d3b) (xorR32R32Effect 0x100d3b 3 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d3b 3 0 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d3b 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x100d3e [0x44, 0x8B, 0x54, 0x24, 0x2C] (LoadPre 0x100d3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100d3e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100d3e 10 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x100d3e 10 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r32_m32_effect_step 0x100d3e 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f149 : InstrSpec 0x100d43 [0x41, 0x21, 0xC2] (fun s => s.RIP = 0x100d43) (andR32R32Effect 0x100d43 3 10 0)
      [.gpr 10, .gpr 0] [] [.reg 10, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100d43 3 10 0).toInstrSpec (and_r32_r32_rex_effect_step 0x100d43 0x41 0xc2 (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x100d46 [0x41, 0x31, 0xEA] (fun s => s.RIP = 0x100d46) (xorR32R32Effect 0x100d46 3 10 5)
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d46 3 10 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d46 0x41 0xea (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x100d49 [0x44, 0x89, 0xD5] (fun s => s.RIP = 0x100d49) (movR32R32Effect 0x100d49 3 5 10)
      [.gpr 10] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x100d49 3 5 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x100d49 0x44 0xd5 (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x100d4c [0x23, 0x44, 0x24, 0x30] (LoadPre 0x100d4c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100d4c + BitVec.ofNat 64 4)) 4) (andR32M32Effect 0x100d4c 4 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (andR32M32Effect_footprint 0x100d4c 4 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (and_r32_m32_effect_step 0x100d4c 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f153 : InstrSpec 0x100d50 [0x44, 0x8B, 0x74, 0x24, 0x28] (LoadPre 0x100d50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100d50 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100d50 14 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x100d50 14 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_effect_step 0x100d50 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f154 : InstrSpec 0x100d55 [0x45, 0x21, 0xEE] (fun s => s.RIP = 0x100d55) (andR32R32Effect 0x100d55 3 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100d55 3 14 13).toInstrSpec (and_r32_r32_rex_effect_step 0x100d55 0x45 0xee (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x100d58 [0x44, 0x23, 0x6C, 0x24, 0x34] (LoadPre 0x100d58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100d58 + BitVec.ofNat 64 5)) 4) (andR32M32Effect 0x100d58 5 13 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (andR32M32Effect_footprint 0x100d58 5 13 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (and_r32_m32_rex_effect_step 0x100d58 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f156 : InstrSpec 0x100d5d [0x44, 0x8B, 0x54, 0x24, 0x04] (LoadPre 0x100d5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100d5d + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100d5d 10 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x100d5d 10 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x100d5d 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f157 : InstrSpec 0x100d62 [0x41, 0x21, 0xCA] (fun s => s.RIP = 0x100d62) (andR32R32Effect 0x100d62 3 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100d62 3 10 1).toInstrSpec (and_r32_r32_rex_effect_step 0x100d62 0x41 0xca (by decide) (by decide)) pre_rip
  have f158 : InstrSpec 0x100d65 [0x44, 0x31, 0xE8] (fun s => s.RIP = 0x100d65) (xorR32R32Effect 0x100d65 3 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d65 3 0 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d65 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x100d68 [0x31, 0xC2] (fun s => s.RIP = 0x100d68) (xorR32R32Effect 0x100d68 2 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d68 2 2 0).toInstrSpec (xor_r32_r32_effect_step 0x100d68 0xc2 (by decide)) pre_rip
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f140 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 312), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d29) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f141 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 312), (13, 272), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d2c) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f142 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 321) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 320), (9, 290), (10, 220), (11, 296), (12, 312), (13, 272), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d2f) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.exec (n := 322) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 320), (9, 290), (10, 220), (11, 296), (12, 312), (13, 272), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d32) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f144 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 324) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 320), (9, 290), (10, 220), (11, 296), (12, 323), (13, 272), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d35) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 325) (RestInside.out (n := 325) f145 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 326) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 320), (9, 290), (10, 220), (11, 296), (12, 325), (13, 272), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d38) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 327) (RestInside.out (n := 327) f146 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 328) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 320), (9, 290), (10, 220), (11, 296), (12, 325), (13, 327), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d3b) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 329) (RestInside.out (n := 329) f147 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 330) (ρ' := [(0, 329), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 320), (9, 290), (10, 220), (11, 296), (12, 325), (13, 327), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d3e) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 331) (RestInside.out (n := 331) f148 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 332) (ρ' := [(0, 329), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 320), (9, 290), (10, 331), (11, 296), (12, 325), (13, 327), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d43) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 333) (RestInside.out (n := 333) f149 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 334) (ρ' := [(0, 329), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 320), (9, 290), (10, 333), (11, 296), (12, 325), (13, 327), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d46) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 335) (RestInside.out (n := 335) f150 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 336) (ρ' := [(0, 329), (1, 274), (2, 310), (3, 53), (4, 4), (5, 316), (6, 300), (7, 302), (8, 320), (9, 290), (10, 335), (11, 296), (12, 325), (13, 327), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d49) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 337) (RestInside.out (n := 337) f151 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 338) (ρ' := [(0, 329), (1, 274), (2, 310), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 335), (11, 296), (12, 325), (13, 327), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d4c) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f152 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 340) (ρ' := [(0, 339), (1, 274), (2, 310), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 335), (11, 296), (12, 325), (13, 327), (14, 288), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d50) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f153 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 342) (ρ' := [(0, 339), (1, 274), (2, 310), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 335), (11, 296), (12, 325), (13, 327), (14, 341), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d55) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 343) (RestInside.out (n := 343) f154 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 344) (ρ' := [(0, 339), (1, 274), (2, 310), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 335), (11, 296), (12, 325), (13, 327), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d58) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 345) (RestInside.out (n := 345) f155 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 346) (ρ' := [(0, 339), (1, 274), (2, 310), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 335), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d5d) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 347) (RestInside.out (n := 347) f156 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 348) (ρ' := [(0, 339), (1, 274), (2, 310), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 347), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d62) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 349) (RestInside.out (n := 349) f157 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 350) (ρ' := [(0, 339), (1, 274), (2, 310), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 349), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d65) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f158 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 351), (1, 274), (2, 310), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 349), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d68) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f159 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 351), (1, 274), (2, 353), (3, 53), (4, 4), (5, 337), (6, 300), (7, 302), (8, 320), (9, 290), (10, 349), (11, 296), (12, 325), (13, 345), (14, 343), (15, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d6a) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100b6d_8 code

theorem rest_l100b6d_6 [Bindings] (code : CodeMap) :
    Rest (n := 278) code lifted (codeRange 0x100b6d bytes_l100b6d) [(0, 264), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 276), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 272), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]
      80 0x100ce4 bytes_l100b6d_6 b_l100b6d_6 := by
  have f120 : InstrSpec 0x100ce4 [0x31, 0xF0] (fun s => s.RIP = 0x100ce4) (xorR32R32Effect 0x100ce4 2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ce4 2 0 6).toInstrSpec (xor_r32_r32_effect_step 0x100ce4 0xf0 (by decide)) pre_rip
  have f121 : InstrSpec 0x100ce6 [0x44, 0x21, 0xE8] (fun s => s.RIP = 0x100ce6) (andR32R32Effect 0x100ce6 3 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100ce6 3 0 13).toInstrSpec (and_r32_r32_rex_effect_step 0x100ce6 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x100ce9 [0x44, 0x31, 0xC8] (fun s => s.RIP = 0x100ce9) (xorR32R32Effect 0x100ce9 3 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ce9 3 0 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x100ce9 0x44 0xc8 (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x100cec [0x41, 0x89, 0xC1] (fun s => s.RIP = 0x100cec) (movR32R32Effect 0x100cec 3 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x100cec 3 9 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x100cec 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x100cef [0x45, 0x31, 0xE9] (fun s => s.RIP = 0x100cef) (xorR32R32Effect 0x100cef 3 9 13)
      [.gpr 9, .gpr 13] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cef 3 9 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cef 0x45 0xe9 (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x100cf2 [0x45, 0x21, 0xCE] (fun s => s.RIP = 0x100cf2) (andR32R32Effect 0x100cf2 3 14 9)
      [.gpr 14, .gpr 9] [] [.reg 14, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100cf2 3 14 9).toInstrSpec (and_r32_r32_rex_effect_step 0x100cf2 0x45 0xce (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x100cf5 [0x44, 0x23, 0x4C, 0x24, 0x08] (LoadPre 0x100cf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100cf5 + BitVec.ofNat 64 5)) 4) (andR32M32Effect 0x100cf5 5 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (andR32M32Effect_footprint 0x100cf5 5 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (and_r32_m32_rex_effect_step 0x100cf5 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f127 : InstrSpec 0x100cfa [0x44, 0x31, 0xDE] (fun s => s.RIP = 0x100cfa) (xorR32R32Effect 0x100cfa 3 6 11)
      [.gpr 6, .gpr 11] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cfa 3 6 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cfa 0x44 0xde (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x100cfd [0x44, 0x8B, 0x5C, 0x24, 0x1C] (LoadPre 0x100cfd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100cfd + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cfd 11 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x100cfd 11 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x100cfd 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f129 : InstrSpec 0x100d02 [0x41, 0x21, 0xF3] (fun s => s.RIP = 0x100d02) (andR32R32Effect 0x100d02 3 11 6)
      [.gpr 11, .gpr 6] [] [.reg 11, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100d02 3 11 6).toInstrSpec (and_r32_r32_rex_effect_step 0x100d02 0x41 0xf3 (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x100d05 [0x41, 0x89, 0xF4] (fun s => s.RIP = 0x100d05) (movR32R32Effect 0x100d05 3 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x100d05 3 12 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x100d05 0x41 0xf4 (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x100d08 [0x23, 0x74, 0x24, 0x20] (LoadPre 0x100d08 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100d08 + BitVec.ofNat 64 4)) 4) (andR32M32Effect 0x100d08 4 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (andR32M32Effect_footprint 0x100d08 4 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (and_r32_m32_effect_step 0x100d08 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f132 : InstrSpec 0x100d0c [0x21, 0xC7] (fun s => s.RIP = 0x100d0c) (andR32R32Effect 0x100d0c 2 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100d0c 2 7 0).toInstrSpec (and_r32_r32_effect_step 0x100d0c 0xc7 (by decide)) pre_rip
  have f133 : InstrSpec 0x100d0e [0x21, 0xC5] (fun s => s.RIP = 0x100d0e) (andR32R32Effect 0x100d0e 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100d0e 2 5 0).toInstrSpec (and_r32_r32_effect_step 0x100d0e 0xc5 (by decide)) pre_rip
  have f134 : InstrSpec 0x100d10 [0x41, 0x31, 0xCC] (fun s => s.RIP = 0x100d10) (xorR32R32Effect 0x100d10 3 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d10 3 12 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d10 0x41 0xcc (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x100d13 [0x44, 0x31, 0xE0] (fun s => s.RIP = 0x100d13) (xorR32R32Effect 0x100d13 3 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100d13 3 0 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100d13 0x44 0xe0 (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x100d16 [0x44, 0x21, 0xE2] (fun s => s.RIP = 0x100d16) (andR32R32Effect 0x100d16 3 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100d16 3 2 12).toInstrSpec (and_r32_r32_rex_effect_step 0x100d16 0x44 0xe2 (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x100d19 [0x45, 0x21, 0xD4] (fun s => s.RIP = 0x100d19) (andR32R32Effect 0x100d19 3 12 10)
      [.gpr 12, .gpr 10] [] [.reg 12, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100d19 3 12 10).toInstrSpec (and_r32_r32_rex_effect_step 0x100d19 0x45 0xd4 (by decide) (by decide)) pre_rip
  have f138 : InstrSpec 0x100d1c [0x44, 0x21, 0x6C, 0x24, 0x10] (StorePre 0x100d1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100d1c + BitVec.ofNat 64 5)) 4) (andMREffect 0x100d1c 5 32 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 13, .gpr 4] [] [.flags, .rip] :=
    (andMREffect32_footprint 0x100d1c 5 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (and_m32_r32_rex_effect_step 0x100d1c 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f139 : InstrSpec 0x100d21 [0x44, 0x21, 0x6C, 0x24, 0x0C] (StorePre 0x100d21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100d21 + BitVec.ofNat 64 5)) 4) (andMREffect 0x100d21 5 32 13 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 13, .gpr 4] [] [.flags, .rip] :=
    (andMREffect32_footprint 0x100d21 5 13 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (and_m32_r32_rex_effect_step 0x100d21 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f120 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 278), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 276), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 272), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce6) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f121 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 280), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 276), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 272), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce9) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f122 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 276), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 272), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cec) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f123 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 276), (7, 206), (8, 127), (9, 284), (10, 220), (11, 240), (12, 198), (13, 272), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cef) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f124 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 276), (7, 206), (8, 127), (9, 286), (10, 220), (11, 240), (12, 198), (13, 272), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cf2) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f125 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 276), (7, 206), (8, 127), (9, 286), (10, 220), (11, 240), (12, 198), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cf5) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f126 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 276), (7, 206), (8, 127), (9, 290), (10, 220), (11, 240), (12, 198), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cfa) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f127 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 292), (7, 206), (8, 127), (9, 290), (10, 220), (11, 240), (12, 198), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cfd) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f128 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 295) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 292), (7, 206), (8, 127), (9, 290), (10, 220), (11, 294), (12, 198), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d02) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.out (n := 296) f129 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 297) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 292), (7, 206), (8, 127), (9, 290), (10, 220), (11, 296), (12, 198), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d05) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f130 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 292), (7, 206), (8, 127), (9, 290), (10, 220), (11, 296), (12, 298), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d08) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f131 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 300), (7, 206), (8, 127), (9, 290), (10, 220), (11, 296), (12, 298), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d0c) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f132 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 298), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d0e) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f133 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 304), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 298), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d10) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f134 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 282), (1, 274), (2, 224), (3, 53), (4, 4), (5, 304), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 306), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d13) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f135 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 308), (1, 274), (2, 224), (3, 53), (4, 4), (5, 304), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 306), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d16) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f136 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 311) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 304), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 306), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d19) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 312) (RestInside.out (n := 312) f137 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 313) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 304), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 312), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d1c) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 314) (RestInside.exec (n := 314) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 304), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 312), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d21) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 315) (RestInside.exec (n := 315) (ρ' := [(0, 308), (1, 274), (2, 310), (3, 53), (4, 4), (5, 304), (6, 300), (7, 302), (8, 127), (9, 290), (10, 220), (11, 296), (12, 312), (13, 272), (14, 288), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100d26) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l100b6d_7 code

theorem rest_l100b6d_5 [Bindings] (code : CodeMap) :
    Rest (n := 238) code lifted (codeRange 0x100b6d bytes_l100b6d) [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 234), (10, 220), (11, 236), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]
      100 0x100ca9 bytes_l100b6d_5 b_l100b6d_5 := by
  have f100 : InstrSpec 0x100ca9 [0x44, 0x8B, 0x74, 0x24, 0x14] (LoadPre 0x100ca9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100ca9 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100ca9 14 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x100ca9 14 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_effect_step 0x100ca9 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f101 : InstrSpec 0x100cae [0x45, 0x31, 0xF3] (fun s => s.RIP = 0x100cae) (xorR32R32Effect 0x100cae 3 11 14)
      [.gpr 11, .gpr 14] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cae 3 11 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cae 0x45 0xf3 (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x100cb1 [0x45, 0x89, 0xDD] (fun s => s.RIP = 0x100cb1) (movR32R32Effect 0x100cb1 3 13 11)
      [.gpr 11] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x100cb1 3 13 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x100cb1 0x45 0xdd (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x100cb4 [0x45, 0x21, 0xCD] (fun s => s.RIP = 0x100cb4) (andR32R32Effect 0x100cb4 3 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100cb4 3 13 9).toInstrSpec (and_r32_r32_rex_effect_step 0x100cb4 0x45 0xcd (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x100cb7 [0x44, 0x89, 0xE9] (fun s => s.RIP = 0x100cb7) (movR32R32Effect 0x100cb7 3 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x100cb7 3 1 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x100cb7 0x44 0xe9 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x100cba [0x44, 0x31, 0xE1] (fun s => s.RIP = 0x100cba) (xorR32R32Effect 0x100cba 3 1 12)
      [.gpr 1, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cba 3 1 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cba 0x44 0xe1 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x100cbd [0x31, 0xC6] (fun s => s.RIP = 0x100cbd) (xorR32R32Effect 0x100cbd 2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cbd 2 6 0).toInstrSpec (xor_r32_r32_effect_step 0x100cbd 0xc6 (by decide)) pre_rip
  have f107 : InstrSpec 0x100cbf [0x21, 0xCE] (fun s => s.RIP = 0x100cbf) (andR32R32Effect 0x100cbf 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100cbf 2 6 1).toInstrSpec (and_r32_r32_effect_step 0x100cbf 0xce (by decide)) pre_rip
  have f108 : InstrSpec 0x100cc1 [0x41, 0x89, 0xC7] (fun s => s.RIP = 0x100cc1) (movR32R32Effect 0x100cc1 3 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x100cc1 3 15 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x100cc1 0x41 0xc7 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x100cc4 [0x45, 0x31, 0xF7] (fun s => s.RIP = 0x100cc4) (xorR32R32Effect 0x100cc4 3 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cc4 3 15 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cc4 0x45 0xf7 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x100cc7 [0x89, 0xF1] (fun s => s.RIP = 0x100cc7) (movR32R32Effect 0x100cc7 2 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x100cc7 2 1 6).toInstrSpec (mov_r32_r32_effect_step 0x100cc7 0xf1 (by decide)) pre_rip
  have f111 : InstrSpec 0x100cc9 [0x44, 0x31, 0xEE] (fun s => s.RIP = 0x100cc9) (xorR32R32Effect 0x100cc9 3 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cc9 3 6 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cc9 0x44 0xee (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x100ccc [0x44, 0x89, 0xE8] (fun s => s.RIP = 0x100ccc) (movR32R32Effect 0x100ccc 3 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x100ccc 3 0 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x100ccc 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x100ccf [0x44, 0x31, 0xF8] (fun s => s.RIP = 0x100ccf) (xorR32R32Effect 0x100ccf 3 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ccf 3 0 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x100ccf 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x100cd2 [0x45, 0x31, 0xE1] (fun s => s.RIP = 0x100cd2) (xorR32R32Effect 0x100cd2 3 9 12)
      [.gpr 9, .gpr 12] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cd2 3 9 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cd2 0x45 0xe1 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x100cd5 [0x41, 0x89, 0xC5] (fun s => s.RIP = 0x100cd5) (movR32R32Effect 0x100cd5 3 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x100cd5 3 13 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x100cd5 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x100cd8 [0x45, 0x21, 0xCD] (fun s => s.RIP = 0x100cd8) (andR32R32Effect 0x100cd8 3 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100cd8 3 13 9).toInstrSpec (and_r32_r32_rex_effect_step 0x100cd8 0x45 0xcd (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x100cdb [0x45, 0x31, 0xE5] (fun s => s.RIP = 0x100cdb) (xorR32R32Effect 0x100cdb 3 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cdb 3 13 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cdb 0x45 0xe5 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x100cde [0x44, 0x31, 0xF9] (fun s => s.RIP = 0x100cde) (xorR32R32Effect 0x100cde 3 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100cde 3 1 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x100cde 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x100ce1 [0x44, 0x21, 0xFE] (fun s => s.RIP = 0x100ce1) (andR32R32Effect 0x100ce1 3 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100ce1 3 6 15).toInstrSpec (and_r32_r32_rex_effect_step 0x100ce1 0x44 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f100 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 234), (10, 220), (11, 236), (12, 198), (13, 190), (14, 238), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cae) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f101 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 190), (14, 238), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cb1) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f102 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 242), (14, 238), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cb4) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f103 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cb7) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f104 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 202), (1, 246), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cba) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f105 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 202), (1, 248), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cbd) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f106 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 202), (1, 248), (2, 224), (3, 53), (4, 4), (5, 156), (6, 250), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cbf) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f107 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 202), (1, 248), (2, 224), (3, 53), (4, 4), (5, 156), (6, 252), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cc1) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f108 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 202), (1, 248), (2, 224), (3, 53), (4, 4), (5, 156), (6, 252), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 254), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cc4) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f109 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 257) (ρ' := [(0, 202), (1, 248), (2, 224), (3, 53), (4, 4), (5, 156), (6, 252), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cc7) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.out (n := 258) f110 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 259) (ρ' := [(0, 202), (1, 258), (2, 224), (3, 53), (4, 4), (5, 156), (6, 252), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cc9) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 260) (RestInside.out (n := 260) f111 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 261) (ρ' := [(0, 202), (1, 258), (2, 224), (3, 53), (4, 4), (5, 156), (6, 260), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ccc) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f112 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 262), (1, 258), (2, 224), (3, 53), (4, 4), (5, 156), (6, 260), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ccf) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f113 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 264), (1, 258), (2, 224), (3, 53), (4, 4), (5, 156), (6, 260), (7, 206), (8, 127), (9, 234), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cd2) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f114 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 264), (1, 258), (2, 224), (3, 53), (4, 4), (5, 156), (6, 260), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 244), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cd5) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f115 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 264), (1, 258), (2, 224), (3, 53), (4, 4), (5, 156), (6, 260), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 268), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cd8) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f116 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 264), (1, 258), (2, 224), (3, 53), (4, 4), (5, 156), (6, 260), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 270), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cdb) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f117 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 264), (1, 258), (2, 224), (3, 53), (4, 4), (5, 156), (6, 260), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 272), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100cde) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f118 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 264), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 260), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 272), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce1) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f119 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 264), (1, 274), (2, 224), (3, 53), (4, 4), (5, 156), (6, 276), (7, 206), (8, 127), (9, 266), (10, 220), (11, 240), (12, 198), (13, 272), (14, 238), (15, 256), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ce4) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100b6d_6 code

theorem rest_l100b6d_4 [Bindings] (code : CodeMap) :
    Rest (n := 198) code lifted (codeRange 0x100b6d bytes_l100b6d) [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 196), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]
      120 0x100c72 bytes_l100b6d_4 b_l100b6d_4 := by
  have f80 : InstrSpec 0x100c72 [0x41, 0x31, 0xC4] (fun s => s.RIP = 0x100c72) (xorR32R32Effect 0x100c72 3 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c72 3 12 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c72 0x41 0xc4 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x100c75 [0x44, 0x31, 0xD0] (fun s => s.RIP = 0x100c75) (xorR32R32Effect 0x100c75 3 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c75 3 0 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c75 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x100c78 [0x31, 0xF0] (fun s => s.RIP = 0x100c78) (xorR32R32Effect 0x100c78 2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c78 2 0 6).toInstrSpec (xor_r32_r32_effect_step 0x100c78 0xf0 (by decide)) pre_rip
  have f83 : InstrSpec 0x100c7a [0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x100c7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100c7a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100c7a 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x100c7a 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x100c7a 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f84 : InstrSpec 0x100c7e [0x31, 0xEF] (fun s => s.RIP = 0x100c7e) (xorR32R32Effect 0x100c7e 2 7 5)
      [.gpr 7, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c7e 2 7 5).toInstrSpec (xor_r32_r32_effect_step 0x100c7e 0xef (by decide)) pre_rip
  have f85 : InstrSpec 0x100c80 [0x89, 0xFE] (fun s => s.RIP = 0x100c80) (movR32R32Effect 0x100c80 2 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x100c80 2 6 7).toInstrSpec (mov_r32_r32_effect_step 0x100c80 0xfe (by decide)) pre_rip
  have f86 : InstrSpec 0x100c82 [0x21, 0xEE] (fun s => s.RIP = 0x100c82) (andR32R32Effect 0x100c82 2 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100c82 2 6 5).toInstrSpec (and_r32_r32_effect_step 0x100c82 0xee (by decide)) pre_rip
  have f87 : InstrSpec 0x100c84 [0x44, 0x31, 0xFE] (fun s => s.RIP = 0x100c84) (xorR32R32Effect 0x100c84 3 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c84 3 6 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c84 0x44 0xfe (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x100c87 [0x44, 0x31, 0xD6] (fun s => s.RIP = 0x100c87) (xorR32R32Effect 0x100c87 3 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c87 3 6 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c87 0x44 0xd6 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x100c8a [0x41, 0x31, 0xD1] (fun s => s.RIP = 0x100c8a) (xorR32R32Effect 0x100c8a 3 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c8a 3 9 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c8a 0x41 0xd1 (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x100c8d [0x45, 0x89, 0xF2] (fun s => s.RIP = 0x100c8d) (movR32R32Effect 0x100c8d 3 10 14)
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x100c8d 3 10 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c8d 0x45 0xf2 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x100c90 [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x100c90) (xorR32R32Effect 0x100c90 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c90 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c90 0x45 0xda (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x100c93 [0x89, 0xFA] (fun s => s.RIP = 0x100c93) (movR32R32Effect 0x100c93 2 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x100c93 2 2 7).toInstrSpec (mov_r32_r32_effect_step 0x100c93 0xfa (by decide)) pre_rip
  have f93 : InstrSpec 0x100c95 [0x44, 0x31, 0xEA] (fun s => s.RIP = 0x100c95) (xorR32R32Effect 0x100c95 3 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c95 3 2 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c95 0x44 0xea (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x100c98 [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x100c98) (movR32R32Effect 0x100c98 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x100c98 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c98 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x100c9b [0x41, 0x21, 0xD3] (fun s => s.RIP = 0x100c9b) (andR32R32Effect 0x100c9b 3 11 2)
      [.gpr 11, .gpr 2] [] [.reg 11, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100c9b 3 11 2).toInstrSpec (and_r32_r32_rex_effect_step 0x100c9b 0x41 0xd3 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x100c9e [0x45, 0x31, 0xD9] (fun s => s.RIP = 0x100c9e) (xorR32R32Effect 0x100c9e 3 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c9e 3 9 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c9e 0x45 0xd9 (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x100ca1 [0x31, 0xCE] (fun s => s.RIP = 0x100ca1) (xorR32R32Effect 0x100ca1 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ca1 2 6 1).toInstrSpec (xor_r32_r32_effect_step 0x100ca1 0xce (by decide)) pre_rip
  have f98 : InstrSpec 0x100ca3 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x100ca3) (xorR32R32Effect 0x100ca3 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ca3 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x100ca3 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x100ca6 [0x41, 0x89, 0xF3] (fun s => s.RIP = 0x100ca6) (movR32R32Effect 0x100ca6 3 11 6)
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x100ca6 3 11 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x100ca6 0x41 0xf3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f80 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c75) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f81 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 200), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c78) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f82 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c7a) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f83 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 204), (8, 127), (9, 100), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c7e) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f84 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 206), (8, 127), (9, 100), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c80) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f85 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 208), (7, 206), (8, 127), (9, 100), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c82) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f86 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 210), (7, 206), (8, 127), (9, 100), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c84) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f87 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 212), (7, 206), (8, 127), (9, 100), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c87) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f88 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 214), (7, 206), (8, 127), (9, 100), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c8a) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f89 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 214), (7, 206), (8, 127), (9, 216), (10, 178), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c8d) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f90 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 214), (7, 206), (8, 127), (9, 216), (10, 218), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c90) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f91 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 202), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 214), (7, 206), (8, 127), (9, 216), (10, 220), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c93) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f92 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 202), (1, 136), (2, 222), (3, 53), (4, 4), (5, 156), (6, 214), (7, 206), (8, 127), (9, 216), (10, 220), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c95) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f93 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 214), (7, 206), (8, 127), (9, 216), (10, 220), (11, 185), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c98) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f94 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 214), (7, 206), (8, 127), (9, 216), (10, 220), (11, 226), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c9b) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f95 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 229) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 214), (7, 206), (8, 127), (9, 216), (10, 220), (11, 228), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c9e) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f96 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 214), (7, 206), (8, 127), (9, 230), (10, 220), (11, 228), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ca1) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f97 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 230), (10, 220), (11, 228), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ca3) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f98 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 234), (10, 220), (11, 228), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ca6) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f99 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 202), (1, 136), (2, 224), (3, 53), (4, 4), (5, 156), (6, 232), (7, 206), (8, 127), (9, 234), (10, 220), (11, 236), (12, 198), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ca9) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100b6d_5 code

theorem rest_l100b6d_3 [Bindings] (code : CodeMap) :
    Rest (n := 162) code lifted (codeRange 0x100b6d bytes_l100b6d) [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 156), (6, 148), (7, 153), (8, 127), (9, 100), (10, 160), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]
      140 0x100c2a bytes_l100b6d_3 b_l100b6d_3 := by
  have f60 : InstrSpec 0x100c2a [0x44, 0x89, 0x54, 0x24, 0x10] (StorePre 0x100c2a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100c2a + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c2a 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100c2a 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x100c2a 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f61 : InstrSpec 0x100c2f [0x44, 0x21, 0xD6] (fun s => s.RIP = 0x100c2f) (andR32R32Effect 0x100c2f 3 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100c2f 3 6 10).toInstrSpec (and_r32_r32_rex_effect_step 0x100c2f 0x44 0xd6 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x100c32 [0x31, 0xD6] (fun s => s.RIP = 0x100c32) (xorR32R32Effect 0x100c32 2 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c32 2 6 2).toInstrSpec (xor_r32_r32_effect_step 0x100c32 0xd6 (by decide)) pre_rip
  have f63 : InstrSpec 0x100c34 [0x45, 0x89, 0xDE] (fun s => s.RIP = 0x100c34) (movR32R32Effect 0x100c34 3 14 11)
      [.gpr 11] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x100c34 3 14 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c34 0x45 0xde (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x100c37 [0x44, 0x89, 0x5C, 0x24, 0x1C] (StorePre 0x100c37 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100c37 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c37 11 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100c37 11 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m32_r32_effect_step 0x100c37 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f65 : InstrSpec 0x100c3c [0x44, 0x89, 0xDA] (fun s => s.RIP = 0x100c3c) (movR32R32Effect 0x100c3c 3 2 11)
      [.gpr 11] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x100c3c 3 2 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c3c 0x44 0xda (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x100c3f [0x44, 0x21, 0xE2] (fun s => s.RIP = 0x100c3f) (andR32R32Effect 0x100c3f 3 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100c3f 3 2 12).toInstrSpec (and_r32_r32_rex_effect_step 0x100c3f 0x44 0xe2 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x100c42 [0x41, 0x89, 0xFA] (fun s => s.RIP = 0x100c42) (movR32R32Effect 0x100c42 3 10 7)
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x100c42 3 10 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c42 0x41 0xfa (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x100c45 [0x44, 0x8B, 0x7C, 0x24, 0x08] (LoadPre 0x100c45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100c45 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100c45 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x100c45 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x100c45 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f69 : InstrSpec 0x100c4a [0x45, 0x21, 0xFA] (fun s => s.RIP = 0x100c4a) (andR32R32Effect 0x100c4a 3 10 15)
      [.gpr 10, .gpr 15] [] [.reg 10, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100c4a 3 10 15).toInstrSpec (and_r32_r32_rex_effect_step 0x100c4a 0x45 0xfa (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x100c4d [0x44, 0x8B, 0x64, 0x24, 0x04] (LoadPre 0x100c4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100c4d + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100c4d 12 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x100c4d 12 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x100c4d 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f71 : InstrSpec 0x100c52 [0x41, 0x31, 0xEC] (fun s => s.RIP = 0x100c52) (xorR32R32Effect 0x100c52 3 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c52 3 12 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c52 0x41 0xec (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x100c55 [0x44, 0x89, 0x64, 0x24, 0x04] (StorePre 0x100c55 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100c55 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c55 12 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100c55 12 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x100c55 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x100c5a [0x45, 0x89, 0xEB] (fun s => s.RIP = 0x100c5a) (movR32R32Effect 0x100c5a 3 11 13)
      [.gpr 13] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x100c5a 3 11 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c5a 0x45 0xeb (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x100c5d [0x44, 0x89, 0x6C, 0x24, 0x24] (StorePre 0x100c5d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100c5d + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c5d 13 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100c5d 13 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m32_r32_effect_step 0x100c5d 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x100c62 [0x45, 0x21, 0xEC] (fun s => s.RIP = 0x100c62) (andR32R32Effect 0x100c62 3 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100c62 3 12 13).toInstrSpec (and_r32_r32_rex_effect_step 0x100c62 0x45 0xec (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x100c65 [0x44, 0x8B, 0x2C, 0x24] (LoadPre 0x100c65 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100c65 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100c65 13 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x100c65 13 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_effect_step 0x100c65 0x44 (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f77 : InstrSpec 0x100c69 [0x45, 0x31, 0xEC] (fun s => s.RIP = 0x100c69) (xorR32R32Effect 0x100c69 3 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c69 3 12 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c69 0x45 0xec (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x100c6c [0x41, 0x31, 0xD4] (fun s => s.RIP = 0x100c6c) (xorR32R32Effect 0x100c6c 3 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c6c 3 12 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c6c 0x41 0xd4 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x100c6f [0x45, 0x31, 0xC4] (fun s => s.RIP = 0x100c6f) (xorR32R32Effect 0x100c6f 3 12 8)
      [.gpr 12, .gpr 8] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c6f 3 12 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c6f 0x45 0xc4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 162) (RestInside.exec (n := 162) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 156), (6, 148), (7, 153), (8, 127), (9, 100), (10, 160), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c2f) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f61 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 156), (6, 163), (7, 153), (8, 127), (9, 100), (10, 160), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c32) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f62 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 160), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c34) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f63 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 160), (11, 125), (12, 89), (13, 144), (14, 167), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c37) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.exec (n := 169) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 160), (11, 125), (12, 89), (13, 144), (14, 167), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c3c) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f65 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 142), (1, 136), (2, 170), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 160), (11, 125), (12, 89), (13, 144), (14, 167), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c3f) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f66 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 160), (11, 125), (12, 89), (13, 144), (14, 167), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c42) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f67 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 174), (11, 125), (12, 89), (13, 144), (14, 167), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c45) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f68 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 174), (11, 125), (12, 89), (13, 144), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c4a) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f69 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 125), (12, 89), (13, 144), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c4d) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f70 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 125), (12, 180), (13, 144), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c52) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f71 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 125), (12, 182), (13, 144), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c55) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.exec (n := 184) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 125), (12, 182), (13, 144), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c5a) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f73 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 182), (13, 144), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c5d) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.exec (n := 187) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 182), (13, 144), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c62) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f75 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 188), (13, 144), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c65) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f76 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 188), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c69) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f77 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 192), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c6c) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f78 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 194), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c6f) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f79 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 142), (1, 136), (2, 172), (3, 53), (4, 4), (5, 156), (6, 165), (7, 153), (8, 127), (9, 100), (10, 178), (11, 185), (12, 196), (13, 190), (14, 167), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c72) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100b6d_4 code

theorem rest_l100b6d_2 [Bindings] (code : CodeMap) :
    Rest (n := 125) code lifted (codeRange 0x100b6d bytes_l100b6d) [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 123), (9, 100), (11, 72), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]
      160 0x100bee bytes_l100b6d_2 b_l100b6d_2 := by
  have f40 : InstrSpec 0x100bee [0x45, 0x89, 0xEB] (fun s => s.RIP = 0x100bee) (movR32R32Effect 0x100bee 3 11 13)
      [.gpr 13] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x100bee 3 11 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x100bee 0x45 0xeb (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x100bf1 [0x41, 0x31, 0xE8] (fun s => s.RIP = 0x100bf1) (xorR32R32Effect 0x100bf1 3 8 5)
      [.gpr 8, .gpr 5] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100bf1 3 8 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x100bf1 0x41 0xe8 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x100bf4 [0x44, 0x89, 0xF1] (fun s => s.RIP = 0x100bf4) (movR32R32Effect 0x100bf4 3 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x100bf4 3 1 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x100bf4 0x44 0xf1 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x100bf7 [0x44, 0x31, 0xC1] (fun s => s.RIP = 0x100bf7) (xorR32R32Effect 0x100bf7 3 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100bf7 3 1 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x100bf7 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x100bfa [0x89, 0x4C, 0x24, 0x2C] (StorePre 0x100bfa 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100bfa + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bfa 1 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100bfa 1 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_m32_r32_low_effect_step 0x100bfa 1 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x100bfe [0x44, 0x21, 0xF9] (fun s => s.RIP = 0x100bfe) (andR32R32Effect 0x100bfe 3 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100bfe 3 1 15).toInstrSpec (and_r32_r32_rex_effect_step 0x100bfe 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x100c01 [0x31, 0xF1] (fun s => s.RIP = 0x100c01) (xorR32R32Effect 0x100c01 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c01 2 1 6).toInstrSpec (xor_r32_r32_effect_step 0x100c01 0xf1 (by decide)) pre_rip
  have f47 : InstrSpec 0x100c03 [0x44, 0x89, 0xC0] (fun s => s.RIP = 0x100c03) (movR32R32Effect 0x100c03 3 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x100c03 3 0 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c03 0x44 0xc0 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x100c06 [0x21, 0xF8] (fun s => s.RIP = 0x100c06) (andR32R32Effect 0x100c06 2 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100c06 2 0 7).toInstrSpec (and_r32_r32_effect_step 0x100c06 0xf8 (by decide)) pre_rip
  have f49 : InstrSpec 0x100c08 [0x31, 0xF0] (fun s => s.RIP = 0x100c08) (xorR32R32Effect 0x100c08 2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c08 2 0 6).toInstrSpec (xor_r32_r32_effect_step 0x100c08 0xf0 (by decide)) pre_rip
  have f50 : InstrSpec 0x100c0a [0x44, 0x0F, 0xB7, 0x2B] (LoadPre 0x100c0a (fun s => AddrMode.addr (.base 3 .none) s (0x100c0a + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100c0a 4 13 (.base 3 .none))
      [.gpr 3] [] [.reg 13, .rip] :=
    (movzxR32M16Effect_footprint 0x100c0a 4 13 (.base 3 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x100c0a 0x44 (by decide) 5 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f51 : InstrSpec 0x100c0e [0x44, 0x89, 0xF6] (fun s => s.RIP = 0x100c0e) (movR32R32Effect 0x100c0e 3 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x100c0e 3 6 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c0e 0x44 0xf6 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x100c11 [0x44, 0x31, 0xEE] (fun s => s.RIP = 0x100c11) (xorR32R32Effect 0x100c11 3 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c11 3 6 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c11 0x44 0xee (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x100c14 [0x89, 0x74, 0x24, 0x0C] (StorePre 0x100c14 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100c14 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c14 6 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c14 6 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c14 6 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x100c18 [0x44, 0x89, 0xF7] (fun s => s.RIP = 0x100c18) (movR32R32Effect 0x100c18 3 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x100c18 3 7 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c18 0x44 0xf7 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x100c1b [0x31, 0xEF] (fun s => s.RIP = 0x100c1b) (xorR32R32Effect 0x100c1b 2 7 5)
      [.gpr 7, .gpr 5] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c1b 2 7 5).toInstrSpec (xor_r32_r32_effect_step 0x100c1b 0xef (by decide)) pre_rip
  have f56 : InstrSpec 0x100c1d [0x89, 0x7C, 0x24, 0x14] (StorePre 0x100c1d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100c1d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c1d 7 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100c1d 7 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_low_effect_step 0x100c1d 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x100c21 [0x44, 0x31, 0xED] (fun s => s.RIP = 0x100c21) (xorR32R32Effect 0x100c21 3 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c21 3 5 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c21 0x44 0xed (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x100c24 [0x41, 0x89, 0xEA] (fun s => s.RIP = 0x100c24) (movR32R32Effect 0x100c24 3 10 5)
      [.gpr 5] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x100c24 3 10 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x100c24 0x41 0xea (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x100c27 [0x41, 0x31, 0xD2] (fun s => s.RIP = 0x100c27) (xorR32R32Effect 0x100c27 3 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100c27 3 10 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x100c27 0x41 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f40 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 123), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bf1) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f41 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bf4) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 66), (1, 129), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bf7) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 66), (1, 131), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bfa) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.exec (n := 133) (ρ' := [(0, 66), (1, 131), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bfe) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 66), (1, 134), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c01) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 66), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c03) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f47 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 138), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c06) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f48 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 140), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c08) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c0a) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f50 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c0e) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f51 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 146), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c11) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 148), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c14) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.exec (n := 150) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 148), (7, 118), (8, 127), (9, 100), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c18) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 148), (7, 151), (8, 127), (9, 100), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c1b) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f55 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 148), (7, 153), (8, 127), (9, 100), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c1d) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.exec (n := 155) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 121), (6, 148), (7, 153), (8, 127), (9, 100), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c21) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f57 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 156), (6, 148), (7, 153), (8, 127), (9, 100), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c24) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f58 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 156), (6, 148), (7, 153), (8, 127), (9, 100), (10, 158), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c27) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f59 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 142), (1, 136), (2, 68), (3, 53), (4, 4), (5, 156), (6, 148), (7, 153), (8, 127), (9, 100), (10, 160), (11, 125), (12, 89), (13, 144), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100c2a) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100b6d_3 code

theorem rest_l100b6d_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x100b6d bytes_l100b6d) [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 82), (7, 55), (8, 75), (9, 87), (11, 72), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]
      180 0x100bb4 bytes_l100b6d_1 b_l100b6d_1 := by
  have f20 : InstrSpec 0x100bb4 [0x41, 0x89, 0xF4] (fun s => s.RIP = 0x100bb4) (movR32R32Effect 0x100bb4 3 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x100bb4 3 12 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x100bb4 0x41 0xf4 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x100bb7 [0x89, 0x74, 0x24, 0x20] (StorePre 0x100bb7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100bb7 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bb7 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100bb7 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_low_effect_step 0x100bb7 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x100bbb [0x44, 0x89, 0xCE] (fun s => s.RIP = 0x100bbb) (movR32R32Effect 0x100bbb 3 6 9)
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x100bbb 3 6 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x100bbb 0x44 0xce (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x100bbe [0x31, 0xCE] (fun s => s.RIP = 0x100bbe) (xorR32R32Effect 0x100bbe 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100bbe 2 6 1).toInstrSpec (xor_r32_r32_effect_step 0x100bbe 0xce (by decide)) pre_rip
  have f24 : InstrSpec 0x100bc0 [0x41, 0x89, 0xF5] (fun s => s.RIP = 0x100bc0) (movR32R32Effect 0x100bc0 3 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x100bc0 3 13 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x100bc0 0x41 0xf5 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x100bc3 [0x89, 0xCF] (fun s => s.RIP = 0x100bc3) (movR32R32Effect 0x100bc3 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x100bc3 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x100bc3 0xcf (by decide)) pre_rip
  have f26 : InstrSpec 0x100bc5 [0x41, 0x31, 0xC1] (fun s => s.RIP = 0x100bc5) (xorR32R32Effect 0x100bc5 3 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100bc5 3 9 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x100bc5 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x100bc8 [0x89, 0xD1] (fun s => s.RIP = 0x100bc8) (movR32R32Effect 0x100bc8 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x100bc8 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x100bc8 0xd1 (by decide)) pre_rip
  have f28 : InstrSpec 0x100bca [0x44, 0x31, 0xD9] (fun s => s.RIP = 0x100bca) (xorR32R32Effect 0x100bca 3 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100bca 3 1 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x100bca 0x44 0xd9 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x100bcd [0x89, 0x4C, 0x24, 0x34] (StorePre 0x100bcd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100bcd + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bcd 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100bcd 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x100bcd 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x100bd1 [0x45, 0x89, 0xC8] (fun s => s.RIP = 0x100bd1) (movR32R32Effect 0x100bd1 3 8 9)
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x100bd1 3 8 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x100bd1 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x100bd4 [0x41, 0x31, 0xC8] (fun s => s.RIP = 0x100bd4) (xorR32R32Effect 0x100bd4 3 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100bd4 3 8 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x100bd4 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x100bd7 [0x44, 0x89, 0xC6] (fun s => s.RIP = 0x100bd7) (movR32R32Effect 0x100bd7 3 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x100bd7 3 6 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100bd7 0x44 0xc6 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x100bda [0x45, 0x89, 0xC6] (fun s => s.RIP = 0x100bda) (movR32R32Effect 0x100bda 3 14 8)
      [.gpr 8] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x100bda 3 14 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100bda 0x45 0xc6 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x100bdd [0x44, 0x89, 0x44, 0x24, 0x28] (StorePre 0x100bdd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100bdd + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100bdd 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100bdd 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m32_r32_effect_step 0x100bdd 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x100be2 [0x21, 0xCE] (fun s => s.RIP = 0x100be2) (andR32R32Effect 0x100be2 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR32R32Effect_footprint 0x100be2 2 6 1).toInstrSpec (and_r32_r32_effect_step 0x100be2 0xce (by decide)) pre_rip
  have f36 : InstrSpec 0x100be4 [0x31, 0xD7] (fun s => s.RIP = 0x100be4) (xorR32R32Effect 0x100be4 2 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100be4 2 7 2).toInstrSpec (xor_r32_r32_effect_step 0x100be4 0xd7 (by decide)) pre_rip
  have f37 : InstrSpec 0x100be6 [0x89, 0x3C, 0x24] (StorePre 0x100be6 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100be6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x100be6 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100be6 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x100be6 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x100be9 [0x31, 0xC5] (fun s => s.RIP = 0x100be9) (xorR32R32Effect 0x100be9 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100be9 2 5 0).toInstrSpec (xor_r32_r32_effect_step 0x100be9 0xc5 (by decide)) pre_rip
  have f39 : InstrSpec 0x100beb [0x45, 0x89, 0xE8] (fun s => s.RIP = 0x100beb) (movR32R32Effect 0x100beb 3 8 13)
      [.gpr 13] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x100beb 3 8 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x100beb 0x45 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f20 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 82), (7, 55), (8, 75), (9, 87), (11, 72), (12, 89), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bb7) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 82), (7, 55), (8, 75), (9, 87), (11, 72), (12, 89), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bbb) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 92), (7, 55), (8, 75), (9, 87), (11, 72), (12, 89), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bbe) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 94), (7, 55), (8, 75), (9, 87), (11, 72), (12, 89), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bc0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 94), (7, 55), (8, 75), (9, 87), (11, 72), (12, 89), (13, 96), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bc3) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 94), (7, 98), (8, 75), (9, 87), (11, 72), (12, 89), (13, 96), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bc5) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f26 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 94), (7, 98), (8, 75), (9, 100), (11, 72), (12, 89), (13, 96), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bc8) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 66), (1, 102), (2, 68), (3, 53), (4, 4), (5, 64), (6, 94), (7, 98), (8, 75), (9, 100), (11, 72), (12, 89), (13, 96), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bca) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 94), (7, 98), (8, 75), (9, 100), (11, 72), (12, 89), (13, 96), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bcd) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 94), (7, 98), (8, 75), (9, 100), (11, 72), (12, 89), (13, 96), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bd1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f30 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 94), (7, 98), (8, 107), (9, 100), (11, 72), (12, 89), (13, 96), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bd4) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f31 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 94), (7, 98), (8, 109), (9, 100), (11, 72), (12, 89), (13, 96), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bd7) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f32 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 111), (7, 98), (8, 109), (9, 100), (11, 72), (12, 89), (13, 96), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bda) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f33 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 111), (7, 98), (8, 109), (9, 100), (11, 72), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bdd) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 111), (7, 98), (8, 109), (9, 100), (11, 72), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100be2) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f35 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 116), (7, 98), (8, 109), (9, 100), (11, 72), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100be4) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f36 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 116), (7, 118), (8, 109), (9, 100), (11, 72), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100be6) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.exec (n := 120) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 64), (6, 116), (7, 118), (8, 109), (9, 100), (11, 72), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100be9) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f38 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 109), (9, 100), (11, 72), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100beb) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f39 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 66), (1, 104), (2, 68), (3, 53), (4, 4), (5, 121), (6, 116), (7, 118), (8, 123), (9, 100), (11, 72), (12, 89), (13, 96), (14, 113), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bee) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100b6d_2 code

theorem rest_l100b6d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100b6d bytes_l100b6d) (entryMap (live .l100b6d))
      200 0x100b6d bytes_l100b6d b_l100b6d := by
  have f0 : InstrSpec 0x100b6d [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x100b6d) (movR64R64Effect 0x100b6d 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x100b6d 3 7).toInstrSpec (mov_r64_r64_effect_step 0x100b6d 0x48 0xfb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100b70 [0x0F, 0xB7, 0x7F, 0x02] (LoadPre 0x100b70 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x100b70 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b70 4 7 (.base 7 (.d8 0x2)))
      [.gpr 7] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x100b70 4 7 (.base 7 (.d8 0x2))).toInstrSpec (movzx_r32_m16_effect_step 0x100b70 7 (.base 7 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100b74 [0x89, 0x7C, 0x24, 0x18] (StorePre 0x100b74 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100b74 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100b74 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100b74 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x100b74 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100b78 [0x0F, 0xB7, 0x4B, 0x04] (LoadPre 0x100b78 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x100b78 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b78 4 1 (.base 3 (.d8 0x4)))
      [.gpr 3] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x100b78 4 1 (.base 3 (.d8 0x4))).toInstrSpec (movzx_r32_m16_effect_step 0x100b78 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100b7c [0x44, 0x0F, 0xB7, 0x4B, 0x06] (LoadPre 0x100b7c (fun s => AddrMode.addr (.base 3 (.d8 0x6)) s (0x100b7c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x100b7c 5 9 (.base 3 (.d8 0x6)))
      [.gpr 3] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x100b7c 5 9 (.base 3 (.d8 0x6))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x100b7c 0x44 (by decide) 1 (.base 3 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100b81 [0x0F, 0xB7, 0x73, 0x08] (LoadPre 0x100b81 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100b81 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b81 4 6 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x100b81 4 6 (.base 3 (.d8 0x8))).toInstrSpec (movzx_r32_m16_effect_step 0x100b81 6 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x100b85 [0x0F, 0xB7, 0x6B, 0x0A] (LoadPre 0x100b85 (fun s => AddrMode.addr (.base 3 (.d8 0xa)) s (0x100b85 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b85 4 5 (.base 3 (.d8 0xa)))
      [.gpr 3] [] [.reg 5, .rip] :=
    (movzxR32M16Effect_footprint 0x100b85 4 5 (.base 3 (.d8 0xa))).toInstrSpec (movzx_r32_m16_effect_step 0x100b85 5 (.base 3 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x100b89 [0x0F, 0xB7, 0x43, 0x0C] (LoadPre 0x100b89 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x100b89 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b89 4 0 (.base 3 (.d8 0xc)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x100b89 4 0 (.base 3 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x100b89 0 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100b8d [0x0F, 0xB7, 0x53, 0x0E] (LoadPre 0x100b8d (fun s => AddrMode.addr (.base 3 (.d8 0xe)) s (0x100b8d + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x100b8d 4 2 (.base 3 (.d8 0xe)))
      [.gpr 3] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x100b8d 4 2 (.base 3 (.d8 0xe))).toInstrSpec (movzx_r32_m16_effect_step 0x100b8d 2 (.base 3 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x100b91 [0x41, 0x89, 0xF0] (fun s => s.RIP = 0x100b91) (movR32R32Effect 0x100b91 3 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x100b91 3 8 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x100b91 0x41 0xf0 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x100b94 [0x41, 0x89, 0xF3] (fun s => s.RIP = 0x100b94) (movR32R32Effect 0x100b94 3 11 6)
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x100b94 3 11 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x100b94 0x41 0xf3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x100b97 [0x89, 0x74, 0x24, 0x04] (StorePre 0x100b97 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100b97 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100b97 6 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100b97 6 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x100b97 6 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x100b9b [0x41, 0x31, 0xC8] (fun s => s.RIP = 0x100b9b) (xorR32R32Effect 0x100b9b 3 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100b9b 3 8 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x100b9b 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x100b9e [0x89, 0xD6] (fun s => s.RIP = 0x100b9e) (movR32R32Effect 0x100b9e 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x100b9e 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x100b9e 0xd6 (by decide)) pre_rip
  have f14 : InstrSpec 0x100ba0 [0x31, 0xFE] (fun s => s.RIP = 0x100ba0) (xorR32R32Effect 0x100ba0 2 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ba0 2 6 7).toInstrSpec (xor_r32_r32_effect_step 0x100ba0 0xfe (by decide)) pre_rip
  have f15 : InstrSpec 0x100ba2 [0x89, 0x74, 0x24, 0x08] (StorePre 0x100ba2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100ba2 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100ba2 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100ba2 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x100ba2 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x100ba6 [0x44, 0x31, 0xC6] (fun s => s.RIP = 0x100ba6) (xorR32R32Effect 0x100ba6 3 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100ba6 3 6 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x100ba6 0x44 0xc6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x100ba9 [0x45, 0x89, 0xC7] (fun s => s.RIP = 0x100ba9) (movR32R32Effect 0x100ba9 3 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x100ba9 3 15 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x100ba9 0x45 0xc7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x100bac [0x44, 0x89, 0x44, 0x24, 0x30] (StorePre 0x100bac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100bac + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100bac 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100bac 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m32_r32_effect_step 0x100bac 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x100bb1 [0x41, 0x31, 0xF1] (fun s => s.RIP = 0x100bb1) (xorR32R32Effect 0x100bb1 3 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100bb1 3 9 6).toInstrSpec (xor_r32_r32_rex_effect_step 0x100bb1 0x41 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b70) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (7, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b74) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 53), (4, 4), (7, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b78) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 58), (3, 53), (4, 4), (7, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b7c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 58), (3, 53), (4, 4), (7, 55), (9, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b81) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 58), (3, 53), (4, 4), (6, 62), (7, 55), (9, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b85) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 58), (3, 53), (4, 4), (5, 64), (6, 62), (7, 55), (9, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b89) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 58), (3, 53), (4, 4), (5, 64), (6, 62), (7, 55), (9, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b8d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 62), (7, 55), (9, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b91) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 62), (7, 55), (8, 70), (9, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b94) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 62), (7, 55), (8, 70), (9, 60), (11, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b97) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 62), (7, 55), (8, 70), (9, 60), (11, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b9b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 62), (7, 55), (8, 75), (9, 60), (11, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b9e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 77), (7, 55), (8, 75), (9, 60), (11, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ba0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 79), (7, 55), (8, 75), (9, 60), (11, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ba2) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 79), (7, 55), (8, 75), (9, 60), (11, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ba6) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 82), (7, 55), (8, 75), (9, 60), (11, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100ba9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 82), (7, 55), (8, 75), (9, 60), (11, 72), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bac) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 82), (7, 55), (8, 75), (9, 60), (11, 72), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bb1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 66), (1, 58), (2, 68), (3, 53), (4, 4), (5, 64), (6, 82), (7, 55), (8, 75), (9, 87), (11, 72), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100bb4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l100b6d_1 code

theorem block_l100b6d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100b6d :=
  Rest.liftedBlock (rest_l100b6d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100b6d x hx)

theorem rest_l100de6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100de6 bytes_l100de6) (entryMap (live .l100de6))
      4 0x100de6 bytes_l100de6 b_l100de6 := by
  have f0 : InstrSpec 0x100de6 [0x31, 0xFF] (fun s => s.RIP = 0x100de6) (xorR32R32Effect 0x100de6 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100de6 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x100de6 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x100de8 [0x31, 0xF6] (fun s => s.RIP = 0x100de8) (xorR32R32Effect 0x100de8 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x100de8 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x100de8 0xf6 (by decide)) pre_rip
  have f2 : InstrSpec 0x100dea [0x48, 0xC7, 0xC2, 0x60, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x100dea) (movR64Imm32Effect 0x100dea 2 0x200e60)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100dea 2 0x200e60).toInstrSpec (mov_r64_imm32_effect_step 0x100dea 0x48 0xc2 (by decide) (by decide) (by decide) 0x200e60) pre_rip
  have f3 : InstrSpec 0x100df1 [0xE8, 0x41, 0x2A, 0x00, 0x00] (PushPre 0x100df1 5) (callEffect (fun _ => 0x103837) 0x100df6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100df1 0x103837 0x100df6).toInstrSpec (call_rel32_effect_step 0x100df1 0x2a41 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x100de8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100dea) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100df1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100de6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100de6 :=
  Rest.liftedBlock (rest_l100de6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100de6 x hx)

theorem rest_l100df6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100df6 bytes_l100df6) (entryMap (live .l100df6))
      4 0x100df6 bytes_l100df6 b_l100df6 := by
  have f0 : InstrSpec 0x100df6 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100df6) (movR32Imm32Effect 0x100df6 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100df6 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x100df6 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x100dfb [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100dfb) (movR32Imm32Effect 0x100dfb 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100dfb 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x100dfb 0xbe (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x100e00 [0x48, 0xC7, 0xC2, 0x78, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x100e00) (movR64Imm32Effect 0x100e00 2 0x200e78)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100e00 2 0x200e78).toInstrSpec (mov_r64_imm32_effect_step 0x100e00 0x48 0xc2 (by decide) (by decide) (by decide) 0x200e78) pre_rip
  have f3 : InstrSpec 0x100e07 [0xE8, 0x2B, 0x2A, 0x00, 0x00] (PushPre 0x100e07 5) (callEffect (fun _ => 0x103837) 0x100e0c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e07 0x103837 0x100e0c).toInstrSpec (call_rel32_effect_step 0x100e07 0x2a2b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x100dfb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e00) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e07) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100df6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100df6 :=
  Rest.liftedBlock (rest_l100df6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100df6 x hx)

theorem rest_l100e0c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e0c bytes_l100e0c) (entryMap (live .l100e0c))
      4 0x100e0c bytes_l100e0c b_l100e0c := by
  have f0 : InstrSpec 0x100e0c [0xBF, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e0c) (movR32Imm32Effect 0x100e0c 5 7 0x2)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100e0c 5 7 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x100e0c 0xbf (by decide) 0x2) pre_rip
  have f1 : InstrSpec 0x100e11 [0xBE, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e11) (movR32Imm32Effect 0x100e11 5 6 0x2)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100e11 5 6 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x100e11 0xbe (by decide) 0x2) pre_rip
  have f2 : InstrSpec 0x100e16 [0x48, 0xC7, 0xC2, 0x90, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x100e16) (movR64Imm32Effect 0x100e16 2 0x200e90)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100e16 2 0x200e90).toInstrSpec (mov_r64_imm32_effect_step 0x100e16 0x48 0xc2 (by decide) (by decide) (by decide) 0x200e90) pre_rip
  have f3 : InstrSpec 0x100e1d [0xE8, 0x15, 0x2A, 0x00, 0x00] (PushPre 0x100e1d 5) (callEffect (fun _ => 0x103837) 0x100e22)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e1d 0x103837 0x100e22).toInstrSpec (call_rel32_effect_step 0x100e1d 0x2a15 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x100e11) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e16) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e1d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100e0c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e0c :=
  Rest.liftedBlock (rest_l100e0c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e0c x hx)

theorem rest_l100e22 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e22 bytes_l100e22) (entryMap (live .l100e22))
      4 0x100e22 bytes_l100e22 b_l100e22 := by
  have f0 : InstrSpec 0x100e22 [0xBF, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e22) (movR32Imm32Effect 0x100e22 5 7 0x3)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100e22 5 7 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x100e22 0xbf (by decide) 0x3) pre_rip
  have f1 : InstrSpec 0x100e27 [0xBE, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e27) (movR32Imm32Effect 0x100e27 5 6 0x3)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100e27 5 6 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x100e27 0xbe (by decide) 0x3) pre_rip
  have f2 : InstrSpec 0x100e2c [0x48, 0xC7, 0xC2, 0xA8, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x100e2c) (movR64Imm32Effect 0x100e2c 2 0x200ea8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100e2c 2 0x200ea8).toInstrSpec (mov_r64_imm32_effect_step 0x100e2c 0x48 0xc2 (by decide) (by decide) (by decide) 0x200ea8) pre_rip
  have f3 : InstrSpec 0x100e33 [0xE8, 0xFF, 0x29, 0x00, 0x00] (PushPre 0x100e33 5) (callEffect (fun _ => 0x103837) 0x100e38)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e33 0x103837 0x100e38).toInstrSpec (call_rel32_effect_step 0x100e33 0x29ff (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x100e27) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e2c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e33) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100e22 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e22 :=
  Rest.liftedBlock (rest_l100e22 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e22 x hx)

theorem rest_l100e38 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e38 bytes_l100e38) (entryMap (live .l100e38))
      4 0x100e38 bytes_l100e38 b_l100e38 := by
  have f0 : InstrSpec 0x100e38 [0xBF, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e38) (movR32Imm32Effect 0x100e38 5 7 0x4)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100e38 5 7 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x100e38 0xbf (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x100e3d [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e3d) (movR32Imm32Effect 0x100e3d 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100e3d 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x100e3d 0xbe (by decide) 0x4) pre_rip
  have f2 : InstrSpec 0x100e42 [0x48, 0xC7, 0xC2, 0xC0, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x100e42) (movR64Imm32Effect 0x100e42 2 0x200ec0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100e42 2 0x200ec0).toInstrSpec (mov_r64_imm32_effect_step 0x100e42 0x48 0xc2 (by decide) (by decide) (by decide) 0x200ec0) pre_rip
  have f3 : InstrSpec 0x100e49 [0xE8, 0xE9, 0x29, 0x00, 0x00] (PushPre 0x100e49 5) (callEffect (fun _ => 0x103837) 0x100e4e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e49 0x103837 0x100e4e).toInstrSpec (call_rel32_effect_step 0x100e49 0x29e9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x100e3d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e42) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e49) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100e38 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e38 :=
  Rest.liftedBlock (rest_l100e38 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e38 x hx)

theorem rest_l100e4e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e4e bytes_l100e4e) (entryMap (live .l100e4e))
      4 0x100e4e bytes_l100e4e b_l100e4e := by
  have f0 : InstrSpec 0x100e4e [0xBF, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e4e) (movR32Imm32Effect 0x100e4e 5 7 0x5)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100e4e 5 7 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x100e4e 0xbf (by decide) 0x5) pre_rip
  have f1 : InstrSpec 0x100e53 [0xBE, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e53) (movR32Imm32Effect 0x100e53 5 6 0x5)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100e53 5 6 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x100e53 0xbe (by decide) 0x5) pre_rip
  have f2 : InstrSpec 0x100e58 [0x48, 0xC7, 0xC2, 0xD8, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x100e58) (movR64Imm32Effect 0x100e58 2 0x200ed8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100e58 2 0x200ed8).toInstrSpec (mov_r64_imm32_effect_step 0x100e58 0x48 0xc2 (by decide) (by decide) (by decide) 0x200ed8) pre_rip
  have f3 : InstrSpec 0x100e5f [0xE8, 0xD3, 0x29, 0x00, 0x00] (PushPre 0x100e5f 5) (callEffect (fun _ => 0x103837) 0x100e64)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e5f 0x103837 0x100e64).toInstrSpec (call_rel32_effect_step 0x100e5f 0x29d3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x100e53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e58) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e5f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100e4e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e4e :=
  Rest.liftedBlock (rest_l100e4e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e4e x hx)

theorem rest_l100e64 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e64 bytes_l100e64) (entryMap (live .l100e64))
      4 0x100e64 bytes_l100e64 b_l100e64 := by
  have f0 : InstrSpec 0x100e64 [0xBF, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e64) (movR32Imm32Effect 0x100e64 5 7 0x6)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100e64 5 7 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x100e64 0xbf (by decide) 0x6) pre_rip
  have f1 : InstrSpec 0x100e69 [0xBE, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e69) (movR32Imm32Effect 0x100e69 5 6 0x6)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100e69 5 6 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x100e69 0xbe (by decide) 0x6) pre_rip
  have f2 : InstrSpec 0x100e6e [0x48, 0xC7, 0xC2, 0xF0, 0x0E, 0x20, 0x00] (fun s => s.RIP = 0x100e6e) (movR64Imm32Effect 0x100e6e 2 0x200ef0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100e6e 2 0x200ef0).toInstrSpec (mov_r64_imm32_effect_step 0x100e6e 0x48 0xc2 (by decide) (by decide) (by decide) 0x200ef0) pre_rip
  have f3 : InstrSpec 0x100e75 [0xE8, 0xBD, 0x29, 0x00, 0x00] (PushPre 0x100e75 5) (callEffect (fun _ => 0x103837) 0x100e7a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e75 0x103837 0x100e7a).toInstrSpec (call_rel32_effect_step 0x100e75 0x29bd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x100e69) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e6e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e75) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100e64 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e64 :=
  Rest.liftedBlock (rest_l100e64 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e64 x hx)

theorem rest_l100e7a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100e7a bytes_l100e7a) (entryMap (live .l100e7a))
      4 0x100e7a bytes_l100e7a b_l100e7a := by
  have f0 : InstrSpec 0x100e7a [0xBF, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e7a) (movR32Imm32Effect 0x100e7a 5 7 0x7)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x100e7a 5 7 0x7).toInstrSpec (mov_r32_imm32_effect_step 0x100e7a 0xbf (by decide) 0x7) pre_rip
  have f1 : InstrSpec 0x100e7f [0xBE, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100e7f) (movR32Imm32Effect 0x100e7f 5 6 0x7)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x100e7f 5 6 0x7).toInstrSpec (mov_r32_imm32_effect_step 0x100e7f 0xbe (by decide) 0x7) pre_rip
  have f2 : InstrSpec 0x100e84 [0x48, 0xC7, 0xC2, 0x08, 0x0F, 0x20, 0x00] (fun s => s.RIP = 0x100e84) (movR64Imm32Effect 0x100e84 2 0x200f08)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x100e84 2 0x200f08).toInstrSpec (mov_r64_imm32_effect_step 0x100e84 0x48 0xc2 (by decide) (by decide) (by decide) 0x200f08) pre_rip
  have f3 : InstrSpec 0x100e8b [0xE8, 0xA7, 0x29, 0x00, 0x00] (PushPre 0x100e8b 5) (callEffect (fun _ => 0x103837) 0x100e90)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x100e8b 0x103837 0x100e90).toInstrSpec (call_rel32_effect_step 0x100e8b 0x29a7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x100e7f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e84) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x100e8b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l100e7a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100e7a :=
  Rest.liftedBlock (rest_l100e7a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100e7a x hx)

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

theorem_by block_l100b10_eval :
    program.runBlock (dialect code) ⟨.l100b10, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b27_eval :
    program.runBlock (dialect code) ⟨.l100b27, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b31_eval :
    program.runBlock (dialect code) ⟨.l100b31, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b3b_eval :
    program.runBlock (dialect code) ⟨.l100b3b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b45_eval :
    program.runBlock (dialect code) ⟨.l100b45, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b4f_eval :
    program.runBlock (dialect code) ⟨.l100b4f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b59_eval :
    program.runBlock (dialect code) ⟨.l100b59, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b63_eval :
    program.runBlock (dialect code) ⟨.l100b63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100b6d_eval :
    program.runBlock (dialect code) ⟨.l100b6d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100de6_eval :
    program.runBlock (dialect code) ⟨.l100de6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100df6_eval :
    program.runBlock (dialect code) ⟨.l100df6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e0c_eval :
    program.runBlock (dialect code) ⟨.l100e0c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e22_eval :
    program.runBlock (dialect code) ⟨.l100e22, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e38_eval :
    program.runBlock (dialect code) ⟨.l100e38, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e4e_eval :
    program.runBlock (dialect code) ⟨.l100e4e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e64_eval :
    program.runBlock (dialect code) ⟨.l100e64, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100e7a_eval :
    program.runBlock (dialect code) ⟨.l100e7a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
