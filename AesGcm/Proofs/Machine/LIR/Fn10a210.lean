import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l10a210 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a210 bytes_l10a210) (entryMap (live .l10a210))
      9 0x10a210 bytes_l10a210 b_l10a210 := by
  have f0 : InstrSpec 0x10a210 [0x55] (PushPre 0x10a210 1) (pushR64Effect 0x10a210 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a210 1 5).toInstrSpec (push_r64_effect_step 0x10a210 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10a211 [0x41, 0x57] (PushPre 0x10a211 2) (pushR64Effect 0x10a211 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a211 2 15).toInstrSpec (push_r64_rex_effect_step 0x10a211 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10a213 [0x41, 0x56] (PushPre 0x10a213 2) (pushR64Effect 0x10a213 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a213 2 14).toInstrSpec (push_r64_rex_effect_step 0x10a213 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10a215 [0x41, 0x55] (PushPre 0x10a215 2) (pushR64Effect 0x10a215 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a215 2 13).toInstrSpec (push_r64_rex_effect_step 0x10a215 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10a217 [0x41, 0x54] (PushPre 0x10a217 2) (pushR64Effect 0x10a217 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a217 2 12).toInstrSpec (push_r64_rex_effect_step 0x10a217 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10a219 [0x53] (PushPre 0x10a219 1) (pushR64Effect 0x10a219 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a219 1 3).toInstrSpec (push_r64_effect_step 0x10a219 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10a21a [0x50] (PushPre 0x10a21a 1) (pushR64Effect 0x10a21a 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a21a 1 0).toInstrSpec (push_r64_effect_step 0x10a21a 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10a21b [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x10a21b) (testR64R64Effect 0x10a21b 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x10a21b 2 2).toInstrSpec (test_r64_r64_effect_step 0x10a21b 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a211) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a213) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a215) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a217) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a219) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a21a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a21b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a21e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel32_effect_step 0x10a21e 4 0x3b3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10a210 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a210 :=
  Rest.liftedBlock (rest_l10a210 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a210 x hx)

theorem rest_l10a224 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a224 bytes_l10a224) (entryMap (live .l10a224))
      2 0x10a224 bytes_l10a224 b_l10a224 := by
  have f0 : InstrSpec 0x10a224 [0x48, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x10a224) (cmpR64Imm8Effect 0x10a224 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10a224 2 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x10a224 0x48 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a228) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10a228 4 0x3b9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10a224 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a224 :=
  Rest.liftedBlock (rest_l10a224 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a224 x hx)

theorem rest_l10a22e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a22e bytes_l10a22e) (entryMap (live .l10a22e))
      2 0x10a22e bytes_l10a22e b_l10a22e := by
  have f0 : InstrSpec 0x10a22e [0x48, 0x83, 0xFA, 0x02] (fun s => s.RIP = 0x10a22e) (cmpR64Imm8Effect 0x10a22e 2 0x2)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10a22e 2 0x2).toInstrSpec (cmp_r64_imm8_effect_step 0x10a22e 0x48 0xfa 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a232) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x10a232 6 0x3c5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10a22e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a22e :=
  Rest.liftedBlock (rest_l10a22e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a22e x hx)

theorem rest_l10a238 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a238 bytes_l10a238) (entryMap (live .l10a238))
      2 0x10a238 bytes_l10a238 b_l10a238 := by
  have f0 : InstrSpec 0x10a238 [0x48, 0x83, 0xFA, 0x03] (fun s => s.RIP = 0x10a238) (cmpR64Imm8Effect 0x10a238 2 0x3)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10a238 2 0x3).toInstrSpec (cmp_r64_imm8_effect_step 0x10a238 0x48 0xfa 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a23c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10a23c 4 0x3d1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10a238 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a238 :=
  Rest.liftedBlock (rest_l10a238 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a238 x hx)

theorem rest_l10a242 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a242 bytes_l10a242) (entryMap (live .l10a242))
      2 0x10a242 bytes_l10a242 b_l10a242 := by
  have f0 : InstrSpec 0x10a242 [0x48, 0x83, 0xFA, 0x04] (fun s => s.RIP = 0x10a242) (cmpR64Imm8Effect 0x10a242 2 0x4)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10a242 2 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x10a242 0x48 0xfa 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a246) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x10a246 6 0x3dd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10a242 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a242 :=
  Rest.liftedBlock (rest_l10a242 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a242 x hx)

theorem rest_l10a24c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a24c bytes_l10a24c) (entryMap (live .l10a24c))
      2 0x10a24c bytes_l10a24c b_l10a24c := by
  have f0 : InstrSpec 0x10a24c [0x48, 0x83, 0xFA, 0x05] (fun s => s.RIP = 0x10a24c) (cmpR64Imm8Effect 0x10a24c 2 0x5)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10a24c 2 0x5).toInstrSpec (cmp_r64_imm8_effect_step 0x10a24c 0x48 0xfa 0x5 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a250) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10a250 4 0x3e9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10a24c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a24c :=
  Rest.liftedBlock (rest_l10a24c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a24c x hx)

theorem rest_l10a256 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a256 bytes_l10a256) (entryMap (live .l10a256))
      2 0x10a256 bytes_l10a256 b_l10a256 := by
  have f0 : InstrSpec 0x10a256 [0x48, 0x83, 0xFA, 0x06] (fun s => s.RIP = 0x10a256) (cmpR64Imm8Effect 0x10a256 2 0x6)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10a256 2 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x10a256 0x48 0xfa 0x6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a25a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x10a25a 6 0x3f5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10a256 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a256 :=
  Rest.liftedBlock (rest_l10a256 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a256 x hx)

theorem rest_l10a260 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a260 bytes_l10a260) (entryMap (live .l10a260))
      2 0x10a260 bytes_l10a260 b_l10a260 := by
  have f0 : InstrSpec 0x10a260 [0x48, 0x83, 0xFA, 0x07] (fun s => s.RIP = 0x10a260) (cmpR64Imm8Effect 0x10a260 2 0x7)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10a260 2 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x10a260 0x48 0xfa 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a264) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10a264 4 0x401) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10a260 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a260 :=
  Rest.liftedBlock (rest_l10a260 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a260 x hx)

theorem rest_l10a26a_12 [Bindings] (code : CodeMap) :
    Rest (n := 474) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 414), (1, 466), (2, 471), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]
      19 0x10a5a5 bytes_l10a26a_12 b_l10a26a_12 := by
  have f240 : InstrSpec 0x10a5a5 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10a5a5) (movR64R64Effect 0x10a5a5 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a5a5 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10a5a5 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f241 : InstrSpec 0x10a5a8 [0x88, 0x57, 0x3B] (StorePre 0x10a5a8 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3b)) s (0x10a5a8 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a5a8 3 2 (.base 7 (.d8 0x3b)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a5a8 3 2 (.base 7 (.d8 0x3b))).toInstrSpec (mov_m8_r8_effect_step 0x10a5a8 2 (by decide) (.base 7 (.d8 0x3b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f242 : InstrSpec 0x10a5ab [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x10a5ab) (movR64R64Effect 0x10a5ab 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a5ab 2 0).toInstrSpec (mov_r64_r64_effect_step 0x10a5ab 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f243 : InstrSpec 0x10a5ae [0x88, 0x67, 0x3C] (StorePre 0x10a5ae 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3c)) s (0x10a5ae + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a5ae 3 4 (.base 7 (.d8 0x3c)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a5ae 3 4 (.base 7 (.d8 0x3c))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a5ae 4 (.base 7 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f244 : InstrSpec 0x10a5b1 [0xC1, 0xE8, 0x18] (fun s => s.RIP = 0x10a5b1) (shrR32Effect 0x10a5b1 3 0 24)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a5b1 3 0 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a5b1 0xe8 0x18 (by decide) (by decide)) pre_rip
  have f245 : InstrSpec 0x10a5b4 [0x88, 0x47, 0x3D] (StorePre 0x10a5b4 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3d)) s (0x10a5b4 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a5b4 3 0 (.base 7 (.d8 0x3d)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a5b4 3 0 (.base 7 (.d8 0x3d))).toInstrSpec (mov_m8_r8_effect_step 0x10a5b4 0 (by decide) (.base 7 (.d8 0x3d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f246 : InstrSpec 0x10a5b7 [0x48, 0xC1, 0xE9, 0x28] (fun s => s.RIP = 0x10a5b7) (shrR64Effect 0x10a5b7 4 1 40)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a5b7 4 1 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a5b7 0x48 0xe9 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f247 : InstrSpec 0x10a5bb [0x88, 0x4F, 0x3E] (StorePre 0x10a5bb 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3e)) s (0x10a5bb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a5bb 3 1 (.base 7 (.d8 0x3e)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a5bb 3 1 (.base 7 (.d8 0x3e))).toInstrSpec (mov_m8_r8_effect_step 0x10a5bb 1 (by decide) (.base 7 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f248 : InstrSpec 0x10a5be [0x48, 0xC1, 0xEA, 0x38] (fun s => s.RIP = 0x10a5be) (shrR64Effect 0x10a5be 4 2 56)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a5be 4 2 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a5be 0x48 0xea 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f249 : InstrSpec 0x10a5c2 [0x88, 0x57, 0x3F] (StorePre 0x10a5c2 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3f)) s (0x10a5c2 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a5c2 3 2 (.base 7 (.d8 0x3f)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a5c2 3 2 (.base 7 (.d8 0x3f))).toInstrSpec (mov_m8_r8_effect_step 0x10a5c2 2 (by decide) (.base 7 (.d8 0x3f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f250 : InstrSpec 0x10a5c5 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x10a5c5) (movR64R64Effect 0x10a5c5 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10a5c5 0 7).toInstrSpec (mov_r64_r64_effect_step 0x10a5c5 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f251 : InstrSpec 0x10a5c8 [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x10a5c8) (addR64Imm8Effect 0x10a5c8 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10a5c8 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x10a5c8 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f252 : InstrSpec 0x10a5cc [0x5B] (PopPre 0x10a5cc) (popR64Effect 0x10a5cc 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a5cc 1 3).toInstrSpec (pop_r64_effect_step 0x10a5cc 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f253 : InstrSpec 0x10a5cd [0x41, 0x5C] (PopPre 0x10a5cd) (popR64Effect 0x10a5cd 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a5cd 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10a5cd 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f254 : InstrSpec 0x10a5cf [0x41, 0x5D] (PopPre 0x10a5cf) (popR64Effect 0x10a5cf 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a5cf 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10a5cf 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f255 : InstrSpec 0x10a5d1 [0x41, 0x5E] (PopPre 0x10a5d1) (popR64Effect 0x10a5d1 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a5d1 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10a5d1 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f256 : InstrSpec 0x10a5d3 [0x41, 0x5F] (PopPre 0x10a5d3) (popR64Effect 0x10a5d3 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a5d3 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10a5d3 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f257 : InstrSpec 0x10a5d5 [0x5D] (PopPre 0x10a5d5) (popR64Effect 0x10a5d5 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a5d5 1 5).toInstrSpec (pop_r64_effect_step 0x10a5d5 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f258 : InstrSpec 0x10a5d6 [0xC3] (RetPre 0x10a5d6) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10a5d6).toInstrSpec (ret_effect_step 0x10a5d6) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 474) (RestInside.out (n := 474) f240 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 475) (ρ' := [(0, 414), (1, 474), (2, 471), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5a8) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 476) (RestInside.exec (n := 476) (ρ' := [(0, 414), (1, 474), (2, 471), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5ab) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 477) (RestInside.out (n := 477) f242 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 478) (ρ' := [(0, 414), (1, 474), (2, 477), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5ae) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 479) (RestInside.exec (n := 479) (ρ' := [(0, 414), (1, 474), (2, 477), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5b1) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 480) (RestInside.out (n := 480) f244 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 481) (ρ' := [(0, 480), (1, 474), (2, 477), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5b4) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 482) (RestInside.exec (n := 482) (ρ' := [(0, 480), (1, 474), (2, 477), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5b7) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 483) (RestInside.out (n := 483) f246 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 484) (ρ' := [(0, 480), (1, 483), (2, 477), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5bb) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 485) (RestInside.exec (n := 485) (ρ' := [(0, 480), (1, 483), (2, 477), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5be) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 486) (RestInside.out (n := 486) f248 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 487) (ρ' := [(0, 480), (1, 483), (2, 486), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5c2) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 488) (RestInside.exec (n := 488) (ρ' := [(0, 480), (1, 483), (2, 486), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5c5) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 489) (RestInside.out (n := 489) f250 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 490) (ρ' := [(0, 489), (1, 483), (2, 486), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5c8) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 491) (RestInside.out (n := 491) f251 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 492) (ρ' := [(0, 489), (1, 483), (2, 486), (3, 266), (4, 491), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5cc) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 493) (RestInside.out (n := 493) f252 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 494) f252 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 495) (ρ' := [(0, 489), (1, 483), (2, 486), (3, 493), (4, 494), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5cd) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 496) (RestInside.out (n := 496) f253 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 497) f253 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 498) (ρ' := [(0, 489), (1, 483), (2, 486), (3, 493), (4, 497), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 496), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5cf) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 499) (RestInside.out (n := 499) f254 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 500) f254 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 501) (ρ' := [(0, 489), (1, 483), (2, 486), (3, 493), (4, 500), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 496), (13, 499), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5d1) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 502) (RestInside.out (n := 502) f255 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 503) f255 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 504) (ρ' := [(0, 489), (1, 483), (2, 486), (3, 493), (4, 503), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 496), (13, 499), (14, 502), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5d3) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 505) (RestInside.out (n := 505) f256 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 506) f256 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 507) (ρ' := [(0, 489), (1, 483), (2, 486), (3, 493), (4, 506), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 496), (13, 499), (14, 502), (15, 505), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5d5) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 508) (RestInside.out (n := 508) f257 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 509) f257 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 510) (ρ' := [(0, 489), (1, 483), (2, 486), (3, 493), (4, 509), (5, 508), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 496), (13, 499), (14, 502), (15, 505), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5d6) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 511) (RestInside.out (n := 511) f258 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 512) f258 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 513) (ρ' := [(0, 489), (1, 483), (2, 486), (3, 493), (4, 512), (5, 508), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 496), (13, 499), (14, 502), (15, 505), (22, 22), (39, 39), (50, 50), (51, 51)]) f258 (by decide) rfl rfl rfl (by decide)

theorem rest_l10a26a_11 [Bindings] (code : CodeMap) :
    Rest (n := 443) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 414), (1, 418), (2, 441), (3, 266), (4, 4), (5, 268), (6, 435), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]
      39 0x10a564 bytes_l10a26a_11 b_l10a26a_11 := by
  have f220 : InstrSpec 0x10a564 [0x40, 0x88, 0x77, 0x32] (StorePre 0x10a564 4 (fun s => AddrMode.addr (.base 7 (.d8 0x32)) s (0x10a564 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a564 4 6 (.base 7 (.d8 0x32)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a564 4 6 (.base 7 (.d8 0x32))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a564 0x40 (by decide) 6 (.base 7 (.d8 0x32)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f221 : InstrSpec 0x10a568 [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x10a568) (movR64R64Effect 0x10a568 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10a568 6 1).toInstrSpec (mov_r64_r64_effect_step 0x10a568 0x48 0xce (by decide) (by decide)) pre_rip
  have f222 : InstrSpec 0x10a56b [0x88, 0x57, 0x33] (StorePre 0x10a56b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x33)) s (0x10a56b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a56b 3 2 (.base 7 (.d8 0x33)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a56b 3 2 (.base 7 (.d8 0x33))).toInstrSpec (mov_m8_r8_effect_step 0x10a56b 2 (by decide) (.base 7 (.d8 0x33)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f223 : InstrSpec 0x10a56e [0x89, 0xC2] (fun s => s.RIP = 0x10a56e) (movR32R32Effect 0x10a56e 2 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10a56e 2 2 0).toInstrSpec (mov_r32_r32_effect_step 0x10a56e 0xc2 (by decide)) pre_rip
  have f224 : InstrSpec 0x10a570 [0xC1, 0xEA, 0x10] (fun s => s.RIP = 0x10a570) (shrR32Effect 0x10a570 3 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a570 3 2 16).toInstrSpec (shr_r32_imm8_effect_step 0x10a570 0xea 0x10 (by decide) (by decide)) pre_rip
  have f225 : InstrSpec 0x10a573 [0x88, 0x47, 0x34] (StorePre 0x10a573 3 (fun s => AddrMode.addr (.base 7 (.d8 0x34)) s (0x10a573 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a573 3 0 (.base 7 (.d8 0x34)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a573 3 0 (.base 7 (.d8 0x34))).toInstrSpec (mov_m8_r8_effect_step 0x10a573 0 (by decide) (.base 7 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f226 : InstrSpec 0x10a576 [0x88, 0x57, 0x35] (StorePre 0x10a576 3 (fun s => AddrMode.addr (.base 7 (.d8 0x35)) s (0x10a576 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a576 3 2 (.base 7 (.d8 0x35)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a576 3 2 (.base 7 (.d8 0x35))).toInstrSpec (mov_m8_r8_effect_step 0x10a576 2 (by decide) (.base 7 (.d8 0x35)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f227 : InstrSpec 0x10a579 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x10a579) (movR64R64Effect 0x10a579 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a579 2 0).toInstrSpec (mov_r64_r64_effect_step 0x10a579 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f228 : InstrSpec 0x10a57c [0x48, 0xC1, 0xEA, 0x20] (fun s => s.RIP = 0x10a57c) (shrR64Effect 0x10a57c 4 2 32)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a57c 4 2 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a57c 0x48 0xea 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f229 : InstrSpec 0x10a580 [0x88, 0x57, 0x36] (StorePre 0x10a580 3 (fun s => AddrMode.addr (.base 7 (.d8 0x36)) s (0x10a580 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a580 3 2 (.base 7 (.d8 0x36)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a580 3 2 (.base 7 (.d8 0x36))).toInstrSpec (mov_m8_r8_effect_step 0x10a580 2 (by decide) (.base 7 (.d8 0x36)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f230 : InstrSpec 0x10a583 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x10a583) (movR64R64Effect 0x10a583 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a583 2 0).toInstrSpec (mov_r64_r64_effect_step 0x10a583 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f231 : InstrSpec 0x10a586 [0x48, 0xC1, 0xEA, 0x30] (fun s => s.RIP = 0x10a586) (shrR64Effect 0x10a586 4 2 48)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a586 4 2 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a586 0x48 0xea 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f232 : InstrSpec 0x10a58a [0x88, 0x57, 0x37] (StorePre 0x10a58a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x37)) s (0x10a58a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a58a 3 2 (.base 7 (.d8 0x37)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a58a 3 2 (.base 7 (.d8 0x37))).toInstrSpec (mov_m8_r8_effect_step 0x10a58a 2 (by decide) (.base 7 (.d8 0x37)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f233 : InstrSpec 0x10a58d [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a58d) (movR64R64Effect 0x10a58d 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a58d 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a58d 0x48 0xca (by decide) (by decide)) pre_rip
  have f234 : InstrSpec 0x10a590 [0x88, 0x6F, 0x38] (StorePre 0x10a590 3 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x10a590 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a590 3 5 (.base 7 (.d8 0x38)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a590 3 5 (.base 7 (.d8 0x38))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a590 5 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f235 : InstrSpec 0x10a593 [0xC1, 0xE9, 0x18] (fun s => s.RIP = 0x10a593) (shrR32Effect 0x10a593 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a593 3 1 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a593 0xe9 0x18 (by decide) (by decide)) pre_rip
  have f236 : InstrSpec 0x10a596 [0x88, 0x4F, 0x39] (StorePre 0x10a596 3 (fun s => AddrMode.addr (.base 7 (.d8 0x39)) s (0x10a596 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a596 3 1 (.base 7 (.d8 0x39)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a596 3 1 (.base 7 (.d8 0x39))).toInstrSpec (mov_m8_r8_effect_step 0x10a596 1 (by decide) (.base 7 (.d8 0x39)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f237 : InstrSpec 0x10a599 [0x48, 0xC1, 0xEE, 0x28] (fun s => s.RIP = 0x10a599) (shrR64Effect 0x10a599 4 6 40)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a599 4 6 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a599 0x48 0xee 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f238 : InstrSpec 0x10a59d [0x48, 0xC1, 0xEA, 0x38] (fun s => s.RIP = 0x10a59d) (shrR64Effect 0x10a59d 4 2 56)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a59d 4 2 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a59d 0x48 0xea 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f239 : InstrSpec 0x10a5a1 [0x40, 0x88, 0x77, 0x3A] (StorePre 0x10a5a1 4 (fun s => AddrMode.addr (.base 7 (.d8 0x3a)) s (0x10a5a1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a5a1 4 6 (.base 7 (.d8 0x3a)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a5a1 4 6 (.base 7 (.d8 0x3a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a5a1 0x40 (by decide) 6 (.base 7 (.d8 0x3a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 443) (RestInside.exec (n := 443) (ρ' := [(0, 414), (1, 418), (2, 441), (3, 266), (4, 4), (5, 268), (6, 435), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a568) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 444) (RestInside.out (n := 444) f221 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 445) (ρ' := [(0, 414), (1, 418), (2, 441), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a56b) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 446) (RestInside.exec (n := 446) (ρ' := [(0, 414), (1, 418), (2, 441), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a56e) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 447) (RestInside.out (n := 447) f223 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 448) (ρ' := [(0, 414), (1, 418), (2, 447), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a570) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 449) (RestInside.out (n := 449) f224 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 450) (ρ' := [(0, 414), (1, 418), (2, 449), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a573) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 451) (RestInside.exec (n := 451) (ρ' := [(0, 414), (1, 418), (2, 449), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a576) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 452) (RestInside.exec (n := 452) (ρ' := [(0, 414), (1, 418), (2, 449), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a579) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 453) (RestInside.out (n := 453) f227 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 454) (ρ' := [(0, 414), (1, 418), (2, 453), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a57c) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 455) (RestInside.out (n := 455) f228 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 456) (ρ' := [(0, 414), (1, 418), (2, 455), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a580) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 457) (RestInside.exec (n := 457) (ρ' := [(0, 414), (1, 418), (2, 455), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a583) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 458) (RestInside.out (n := 458) f230 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 459) (ρ' := [(0, 414), (1, 418), (2, 458), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a586) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 460) (RestInside.out (n := 460) f231 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 461) (ρ' := [(0, 414), (1, 418), (2, 460), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a58a) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 462) (RestInside.exec (n := 462) (ρ' := [(0, 414), (1, 418), (2, 460), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a58d) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 463) (RestInside.out (n := 463) f233 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 464) (ρ' := [(0, 414), (1, 418), (2, 463), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a590) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 465) (RestInside.exec (n := 465) (ρ' := [(0, 414), (1, 418), (2, 463), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a593) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 466) (RestInside.out (n := 466) f235 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 467) (ρ' := [(0, 414), (1, 466), (2, 463), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a596) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 468) (RestInside.exec (n := 468) (ρ' := [(0, 414), (1, 466), (2, 463), (3, 266), (4, 4), (5, 268), (6, 444), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a599) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 469) (RestInside.out (n := 469) f237 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 470) (ρ' := [(0, 414), (1, 466), (2, 463), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a59d) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 471) (RestInside.out (n := 471) f238 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 472) (ρ' := [(0, 414), (1, 466), (2, 471), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5a1) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 473) (RestInside.exec (n := 473) (ρ' := [(0, 414), (1, 466), (2, 471), (3, 266), (4, 4), (5, 268), (6, 469), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a5a5) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10a26a_12 code

theorem rest_l10a26a_10 [Bindings] (code : CodeMap) :
    Rest (n := 408) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 248), (1, 406), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]
      59 0x10a521 bytes_l10a26a_10 b_l10a26a_10 := by
  have f200 : InstrSpec 0x10a521 [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x10a521) (shrR64Effect 0x10a521 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a521 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x10a521 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f201 : InstrSpec 0x10a525 [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10a525) (xorR64R64Effect 0x10a525 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a525 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10a525 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f202 : InstrSpec 0x10a528 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x10a528) (andR64R64Effect 0x10a528 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a528 1 9).toInstrSpec (and_r64_r64_effect_step 0x10a528 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f203 : InstrSpec 0x10a52b [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x10a52b) (xorR64R64Effect 0x10a52b 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a52b 0 1).toInstrSpec (xor_r64_r64_effect_step 0x10a52b 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f204 : InstrSpec 0x10a52e [0x48, 0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x10a52e) (shlR64Effect 0x10a52e 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a52e 4 1 4).toInstrSpec (shl_r64_imm8_effect_step 0x10a52e 0x48 0xe1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f205 : InstrSpec 0x10a532 [0x4C, 0x31, 0xF1] (fun s => s.RIP = 0x10a532) (xorR64R64Effect 0x10a532 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a532 1 14).toInstrSpec (xor_r64_r64_effect_step 0x10a532 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f206 : InstrSpec 0x10a535 [0xC1, 0xEA, 0x18] (fun s => s.RIP = 0x10a535) (shrR32Effect 0x10a535 3 2 24)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a535 3 2 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a535 0xea 0x18 (by decide) (by decide)) pre_rip
  have f207 : InstrSpec 0x10a538 [0x88, 0x57, 0x2D] (StorePre 0x10a538 3 (fun s => AddrMode.addr (.base 7 (.d8 0x2d)) s (0x10a538 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a538 3 2 (.base 7 (.d8 0x2d)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a538 3 2 (.base 7 (.d8 0x2d))).toInstrSpec (mov_m8_r8_effect_step 0x10a538 2 (by decide) (.base 7 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f208 : InstrSpec 0x10a53b [0x49, 0xC1, 0xEA, 0x28] (fun s => s.RIP = 0x10a53b) (shrR64Effect 0x10a53b 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a53b 4 10 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a53b 0x49 0xea 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f209 : InstrSpec 0x10a53f [0x49, 0xC1, 0xE8, 0x38] (fun s => s.RIP = 0x10a53f) (shrR64Effect 0x10a53f 4 8 56)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a53f 4 8 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a53f 0x49 0xe8 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f210 : InstrSpec 0x10a543 [0x44, 0x88, 0x57, 0x2E] (StorePre 0x10a543 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2e)) s (0x10a543 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a543 4 10 (.base 7 (.d8 0x2e)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a543 4 10 (.base 7 (.d8 0x2e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a543 0x44 (by decide) 2 (.base 7 (.d8 0x2e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f211 : InstrSpec 0x10a547 [0x89, 0xCA] (fun s => s.RIP = 0x10a547) (movR32R32Effect 0x10a547 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10a547 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x10a547 0xca (by decide)) pre_rip
  have f212 : InstrSpec 0x10a549 [0xC1, 0xEA, 0x10] (fun s => s.RIP = 0x10a549) (shrR32Effect 0x10a549 3 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a549 3 2 16).toInstrSpec (shr_r32_imm8_effect_step 0x10a549 0xea 0x10 (by decide) (by decide)) pre_rip
  have f213 : InstrSpec 0x10a54c [0x44, 0x88, 0x47, 0x2F] (StorePre 0x10a54c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2f)) s (0x10a54c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a54c 4 8 (.base 7 (.d8 0x2f)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a54c 4 8 (.base 7 (.d8 0x2f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a54c 0x44 (by decide) 0 (.base 7 (.d8 0x2f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f214 : InstrSpec 0x10a550 [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x10a550) (movR64R64Effect 0x10a550 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10a550 6 1).toInstrSpec (mov_r64_r64_effect_step 0x10a550 0x48 0xce (by decide) (by decide)) pre_rip
  have f215 : InstrSpec 0x10a553 [0x48, 0xC1, 0xEE, 0x20] (fun s => s.RIP = 0x10a553) (shrR64Effect 0x10a553 4 6 32)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a553 4 6 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a553 0x48 0xee 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f216 : InstrSpec 0x10a557 [0x88, 0x4F, 0x30] (StorePre 0x10a557 3 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10a557 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a557 3 1 (.base 7 (.d8 0x30)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a557 3 1 (.base 7 (.d8 0x30))).toInstrSpec (mov_m8_r8_effect_step 0x10a557 1 (by decide) (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f217 : InstrSpec 0x10a55a [0x88, 0x57, 0x31] (StorePre 0x10a55a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x31)) s (0x10a55a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a55a 3 2 (.base 7 (.d8 0x31)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a55a 3 2 (.base 7 (.d8 0x31))).toInstrSpec (mov_m8_r8_effect_step 0x10a55a 2 (by decide) (.base 7 (.d8 0x31)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f218 : InstrSpec 0x10a55d [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x10a55d) (movR64R64Effect 0x10a55d 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a55d 2 1).toInstrSpec (mov_r64_r64_effect_step 0x10a55d 0x48 0xca (by decide) (by decide)) pre_rip
  have f219 : InstrSpec 0x10a560 [0x48, 0xC1, 0xEA, 0x30] (fun s => s.RIP = 0x10a560) (shrR64Effect 0x10a560 4 2 48)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a560 4 2 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a560 0x48 0xea 0x30 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 408) (RestInside.out (n := 408) f200 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 409) (ρ' := [(0, 248), (1, 408), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a525) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 410) (RestInside.out (n := 410) f201 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 411) (ρ' := [(0, 248), (1, 410), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a528) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 412) (RestInside.out (n := 412) f202 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 413) (ρ' := [(0, 248), (1, 412), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a52b) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 414) (RestInside.out (n := 414) f203 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 415) (ρ' := [(0, 414), (1, 412), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a52e) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f204 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 417) (ρ' := [(0, 414), (1, 416), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a532) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.out (n := 418) f205 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 419) (ρ' := [(0, 414), (1, 418), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a535) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 420) (RestInside.out (n := 420) f206 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 421) (ρ' := [(0, 414), (1, 418), (2, 420), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a538) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 422) (RestInside.exec (n := 422) (ρ' := [(0, 414), (1, 418), (2, 420), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a53b) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 423) (RestInside.out (n := 423) f208 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 424) (ρ' := [(0, 414), (1, 418), (2, 420), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a53f) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f209 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 426) (ρ' := [(0, 414), (1, 418), (2, 420), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a543) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 427) (RestInside.exec (n := 427) (ρ' := [(0, 414), (1, 418), (2, 420), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a547) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f211 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 429) (ρ' := [(0, 414), (1, 418), (2, 428), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a549) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 430) (RestInside.out (n := 430) f212 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 431) (ρ' := [(0, 414), (1, 418), (2, 430), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a54c) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 432) (RestInside.exec (n := 432) (ρ' := [(0, 414), (1, 418), (2, 430), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a550) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 433) (RestInside.out (n := 433) f214 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 434) (ρ' := [(0, 414), (1, 418), (2, 430), (3, 266), (4, 4), (5, 268), (6, 433), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a553) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 435) (RestInside.out (n := 435) f215 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 436) (ρ' := [(0, 414), (1, 418), (2, 430), (3, 266), (4, 4), (5, 268), (6, 435), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a557) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 437) (RestInside.exec (n := 437) (ρ' := [(0, 414), (1, 418), (2, 430), (3, 266), (4, 4), (5, 268), (6, 435), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a55a) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 438) (RestInside.exec (n := 438) (ρ' := [(0, 414), (1, 418), (2, 430), (3, 266), (4, 4), (5, 268), (6, 435), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a55d) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 439) (RestInside.out (n := 439) f218 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 440) (ρ' := [(0, 414), (1, 418), (2, 439), (3, 266), (4, 4), (5, 268), (6, 435), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a560) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 441) (RestInside.out (n := 441) f219 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 442) (ρ' := [(0, 414), (1, 418), (2, 441), (3, 266), (4, 4), (5, 268), (6, 435), (7, 7), (8, 425), (9, 163), (10, 423), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a564) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_11 code

theorem rest_l10a26a_9 [Bindings] (code : CodeMap) :
    Rest (n := 377) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 375), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]
      79 0x10a4dc bytes_l10a26a_9 b_l10a26a_9 := by
  have f180 : InstrSpec 0x10a4dc [0x88, 0x57, 0x24] (StorePre 0x10a4dc 3 (fun s => AddrMode.addr (.base 7 (.d8 0x24)) s (0x10a4dc + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a4dc 3 2 (.base 7 (.d8 0x24)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4dc 3 2 (.base 7 (.d8 0x24))).toInstrSpec (mov_m8_r8_effect_step 0x10a4dc 2 (by decide) (.base 7 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f181 : InstrSpec 0x10a4df [0x40, 0x88, 0x77, 0x25] (StorePre 0x10a4df 4 (fun s => AddrMode.addr (.base 7 (.d8 0x25)) s (0x10a4df + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4df 4 6 (.base 7 (.d8 0x25)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4df 4 6 (.base 7 (.d8 0x25))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a4df 0x40 (by decide) 6 (.base 7 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f182 : InstrSpec 0x10a4e3 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x10a4e3) (movR64R64Effect 0x10a4e3 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10a4e3 6 2).toInstrSpec (mov_r64_r64_effect_step 0x10a4e3 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f183 : InstrSpec 0x10a4e6 [0x48, 0xC1, 0xEE, 0x20] (fun s => s.RIP = 0x10a4e6) (shrR64Effect 0x10a4e6 4 6 32)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a4e6 4 6 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a4e6 0x48 0xee 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f184 : InstrSpec 0x10a4ea [0x40, 0x88, 0x77, 0x26] (StorePre 0x10a4ea 4 (fun s => AddrMode.addr (.base 7 (.d8 0x26)) s (0x10a4ea + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4ea 4 6 (.base 7 (.d8 0x26)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4ea 4 6 (.base 7 (.d8 0x26))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a4ea 0x40 (by decide) 6 (.base 7 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f185 : InstrSpec 0x10a4ee [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x10a4ee) (movR64R64Effect 0x10a4ee 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10a4ee 6 2).toInstrSpec (mov_r64_r64_effect_step 0x10a4ee 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x10a4f1 [0x48, 0xC1, 0xEE, 0x30] (fun s => s.RIP = 0x10a4f1) (shrR64Effect 0x10a4f1 4 6 48)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a4f1 4 6 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a4f1 0x48 0xee 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f187 : InstrSpec 0x10a4f5 [0x40, 0x88, 0x77, 0x27] (StorePre 0x10a4f5 4 (fun s => AddrMode.addr (.base 7 (.d8 0x27)) s (0x10a4f5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4f5 4 6 (.base 7 (.d8 0x27)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4f5 4 6 (.base 7 (.d8 0x27))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a4f5 0x40 (by decide) 6 (.base 7 (.d8 0x27)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f188 : InstrSpec 0x10a4f9 [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x10a4f9) (movR64R64Effect 0x10a4f9 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10a4f9 6 1).toInstrSpec (mov_r64_r64_effect_step 0x10a4f9 0x48 0xce (by decide) (by decide)) pre_rip
  have f189 : InstrSpec 0x10a4fc [0x88, 0x6F, 0x28] (StorePre 0x10a4fc 3 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x10a4fc + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a4fc 3 5 (.base 7 (.d8 0x28)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a4fc 3 5 (.base 7 (.d8 0x28))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a4fc 5 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f190 : InstrSpec 0x10a4ff [0xC1, 0xE9, 0x18] (fun s => s.RIP = 0x10a4ff) (shrR32Effect 0x10a4ff 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a4ff 3 1 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a4ff 0xe9 0x18 (by decide) (by decide)) pre_rip
  have f191 : InstrSpec 0x10a502 [0x49, 0xC1, 0xE8, 0x28] (fun s => s.RIP = 0x10a502) (shrR64Effect 0x10a502 4 8 40)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a502 4 8 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a502 0x49 0xe8 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f192 : InstrSpec 0x10a506 [0x48, 0xC1, 0xEE, 0x38] (fun s => s.RIP = 0x10a506) (shrR64Effect 0x10a506 4 6 56)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a506 4 6 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a506 0x48 0xee 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f193 : InstrSpec 0x10a50a [0x88, 0x4F, 0x29] (StorePre 0x10a50a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x29)) s (0x10a50a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a50a 3 1 (.base 7 (.d8 0x29)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a50a 3 1 (.base 7 (.d8 0x29))).toInstrSpec (mov_m8_r8_effect_step 0x10a50a 1 (by decide) (.base 7 (.d8 0x29)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f194 : InstrSpec 0x10a50d [0x49, 0x89, 0xD2] (fun s => s.RIP = 0x10a50d) (movR64R64Effect 0x10a50d 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10a50d 10 2).toInstrSpec (mov_r64_r64_effect_step 0x10a50d 0x49 0xd2 (by decide) (by decide)) pre_rip
  have f195 : InstrSpec 0x10a510 [0x44, 0x88, 0x47, 0x2A] (StorePre 0x10a510 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2a)) s (0x10a510 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a510 4 8 (.base 7 (.d8 0x2a)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a510 4 8 (.base 7 (.d8 0x2a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a510 0x44 (by decide) 0 (.base 7 (.d8 0x2a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f196 : InstrSpec 0x10a514 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x10a514) (movR64R64Effect 0x10a514 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10a514 8 2).toInstrSpec (mov_r64_r64_effect_step 0x10a514 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f197 : InstrSpec 0x10a517 [0x40, 0x88, 0x77, 0x2B] (StorePre 0x10a517 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2b)) s (0x10a517 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a517 4 6 (.base 7 (.d8 0x2b)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a517 4 6 (.base 7 (.d8 0x2b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a517 0x40 (by decide) 6 (.base 7 (.d8 0x2b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f198 : InstrSpec 0x10a51b [0x88, 0x77, 0x2C] (StorePre 0x10a51b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x2c)) s (0x10a51b + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a51b 3 6 (.base 7 (.d8 0x2c)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a51b 3 6 (.base 7 (.d8 0x2c))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a51b 6 (.base 7 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f199 : InstrSpec 0x10a51e [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x10a51e) (movR64R64Effect 0x10a51e 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a51e 1 14).toInstrSpec (mov_r64_r64_effect_step 0x10a51e 0x4c 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 377) (RestInside.exec (n := 377) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 375), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4df) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 378) (RestInside.exec (n := 378) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 375), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4e3) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 379) (RestInside.out (n := 379) f182 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 380) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 379), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4e6) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 381) (RestInside.out (n := 381) f183 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 382) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 381), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4ea) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 383) (RestInside.exec (n := 383) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 381), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4ee) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 384) (RestInside.out (n := 384) f185 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 385) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 384), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4f1) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 386) (RestInside.out (n := 386) f186 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 387) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 386), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4f5) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 388) (RestInside.exec (n := 388) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 386), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4f9) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f188 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 389), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4fc) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.exec (n := 391) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 389), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4ff) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 392) (RestInside.out (n := 392) f190 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 393) (ρ' := [(0, 248), (1, 392), (2, 340), (3, 266), (4, 4), (5, 268), (6, 389), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a502) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 394) (RestInside.out (n := 394) f191 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 395) (ρ' := [(0, 248), (1, 392), (2, 340), (3, 266), (4, 4), (5, 268), (6, 389), (7, 7), (8, 394), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a506) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 396) (RestInside.out (n := 396) f192 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 397) (ρ' := [(0, 248), (1, 392), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 394), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a50a) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 398) (RestInside.exec (n := 398) (ρ' := [(0, 248), (1, 392), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 394), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a50d) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 399) (RestInside.out (n := 399) f194 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 400) (ρ' := [(0, 248), (1, 392), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 394), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a510) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 401) (RestInside.exec (n := 401) (ρ' := [(0, 248), (1, 392), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 394), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a514) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 402) (RestInside.out (n := 402) f196 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 403) (ρ' := [(0, 248), (1, 392), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a517) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 404) (RestInside.exec (n := 404) (ρ' := [(0, 248), (1, 392), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a51b) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 405) (RestInside.exec (n := 405) (ρ' := [(0, 248), (1, 392), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a51e) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 406) (RestInside.out (n := 406) f199 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 407) (ρ' := [(0, 248), (1, 406), (2, 340), (3, 266), (4, 4), (5, 268), (6, 396), (7, 7), (8, 402), (9, 163), (10, 399), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a521) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_10 code

theorem rest_l10a26a_8 [Bindings] (code : CodeMap) :
    Rest (n := 344) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 248), (1, 342), (2, 340), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 330), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]
      99 0x10a497 bytes_l10a26a_8 b_l10a26a_8 := by
  have f160 : InstrSpec 0x10a497 [0x48, 0x31, 0xF1] (fun s => s.RIP = 0x10a497) (xorR64R64Effect 0x10a497 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a497 1 6).toInstrSpec (xor_r64_r64_effect_step 0x10a497 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x10a49a [0x41, 0xC1, 0xE8, 0x18] (fun s => s.RIP = 0x10a49a) (shrR32Effect 0x10a49a 4 8 24)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a49a 4 8 24).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a49a 0x41 0xe8 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f162 : InstrSpec 0x10a49e [0x44, 0x88, 0x47, 0x1D] (StorePre 0x10a49e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1d)) s (0x10a49e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a49e 4 8 (.base 7 (.d8 0x1d)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a49e 4 8 (.base 7 (.d8 0x1d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a49e 0x44 (by decide) 0 (.base 7 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f163 : InstrSpec 0x10a4a2 [0x49, 0xC1, 0xEB, 0x28] (fun s => s.RIP = 0x10a4a2) (shrR64Effect 0x10a4a2 4 11 40)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a4a2 4 11 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a4a2 0x49 0xeb 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f164 : InstrSpec 0x10a4a6 [0x49, 0xC1, 0xEA, 0x38] (fun s => s.RIP = 0x10a4a6) (shrR64Effect 0x10a4a6 4 10 56)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a4a6 4 10 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a4a6 0x49 0xea 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x10a4aa [0x44, 0x88, 0x5F, 0x1E] (StorePre 0x10a4aa 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1e)) s (0x10a4aa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4aa 4 11 (.base 7 (.d8 0x1e)))
      [.gpr 11, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4aa 4 11 (.base 7 (.d8 0x1e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a4aa 0x44 (by decide) 3 (.base 7 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f166 : InstrSpec 0x10a4ae [0x89, 0xCE] (fun s => s.RIP = 0x10a4ae) (movR32R32Effect 0x10a4ae 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10a4ae 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x10a4ae 0xce (by decide)) pre_rip
  have f167 : InstrSpec 0x10a4b0 [0xC1, 0xEE, 0x10] (fun s => s.RIP = 0x10a4b0) (shrR32Effect 0x10a4b0 3 6 16)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a4b0 3 6 16).toInstrSpec (shr_r32_imm8_effect_step 0x10a4b0 0xee 0x10 (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x10a4b3 [0x44, 0x88, 0x57, 0x1F] (StorePre 0x10a4b3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1f)) s (0x10a4b3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4b3 4 10 (.base 7 (.d8 0x1f)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4b3 4 10 (.base 7 (.d8 0x1f))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a4b3 0x44 (by decide) 2 (.base 7 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f169 : InstrSpec 0x10a4b7 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x10a4b7) (movR64R64Effect 0x10a4b7 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10a4b7 8 1).toInstrSpec (mov_r64_r64_effect_step 0x10a4b7 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x10a4ba [0x49, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x10a4ba) (shrR64Effect 0x10a4ba 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a4ba 4 8 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a4ba 0x49 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x10a4be [0x88, 0x4F, 0x20] (StorePre 0x10a4be 3 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10a4be + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a4be 3 1 (.base 7 (.d8 0x20)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4be 3 1 (.base 7 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x10a4be 1 (by decide) (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f172 : InstrSpec 0x10a4c1 [0x40, 0x88, 0x77, 0x21] (StorePre 0x10a4c1 4 (fun s => AddrMode.addr (.base 7 (.d8 0x21)) s (0x10a4c1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4c1 4 6 (.base 7 (.d8 0x21)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4c1 4 6 (.base 7 (.d8 0x21))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a4c1 0x40 (by decide) 6 (.base 7 (.d8 0x21)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f173 : InstrSpec 0x10a4c5 [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x10a4c5) (movR64R64Effect 0x10a4c5 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10a4c5 6 1).toInstrSpec (mov_r64_r64_effect_step 0x10a4c5 0x48 0xce (by decide) (by decide)) pre_rip
  have f174 : InstrSpec 0x10a4c8 [0x48, 0xC1, 0xEE, 0x30] (fun s => s.RIP = 0x10a4c8) (shrR64Effect 0x10a4c8 4 6 48)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a4c8 4 6 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a4c8 0x48 0xee 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x10a4cc [0x44, 0x88, 0x47, 0x22] (StorePre 0x10a4cc 4 (fun s => AddrMode.addr (.base 7 (.d8 0x22)) s (0x10a4cc + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4cc 4 8 (.base 7 (.d8 0x22)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4cc 4 8 (.base 7 (.d8 0x22))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a4cc 0x44 (by decide) 0 (.base 7 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f176 : InstrSpec 0x10a4d0 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x10a4d0) (movR64R64Effect 0x10a4d0 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10a4d0 8 1).toInstrSpec (mov_r64_r64_effect_step 0x10a4d0 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x10a4d3 [0x40, 0x88, 0x77, 0x23] (StorePre 0x10a4d3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x23)) s (0x10a4d3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a4d3 4 6 (.base 7 (.d8 0x23)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a4d3 4 6 (.base 7 (.d8 0x23))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a4d3 0x40 (by decide) 6 (.base 7 (.d8 0x23)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f178 : InstrSpec 0x10a4d7 [0x89, 0xD6] (fun s => s.RIP = 0x10a4d7) (movR32R32Effect 0x10a4d7 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10a4d7 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x10a4d7 0xd6 (by decide)) pre_rip
  have f179 : InstrSpec 0x10a4d9 [0xC1, 0xEE, 0x10] (fun s => s.RIP = 0x10a4d9) (shrR32Effect 0x10a4d9 3 6 16)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a4d9 3 6 16).toInstrSpec (shr_r32_imm8_effect_step 0x10a4d9 0xee 0x10 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f160 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 330), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a49a) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.out (n := 346) f161 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 347) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 346), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a49e) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.exec (n := 348) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 346), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4a2) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 349) (RestInside.out (n := 349) f163 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 350) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 346), (9, 163), (10, 326), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4a6) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f164 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 346), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4aa) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.exec (n := 353) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 346), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4ae) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 354) (RestInside.out (n := 354) f166 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 355) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 354), (7, 7), (8, 346), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4b0) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 356) (RestInside.out (n := 356) f167 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 357) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 356), (7, 7), (8, 346), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4b3) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 358) (RestInside.exec (n := 358) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 356), (7, 7), (8, 346), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4b7) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f169 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 356), (7, 7), (8, 359), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4ba) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f170 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 356), (7, 7), (8, 361), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4be) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 363) (RestInside.exec (n := 363) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 356), (7, 7), (8, 361), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4c1) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 364) (RestInside.exec (n := 364) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 356), (7, 7), (8, 361), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4c5) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f173 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 365), (7, 7), (8, 361), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4c8) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.out (n := 367) f174 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 368) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 367), (7, 7), (8, 361), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4cc) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.exec (n := 369) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 367), (7, 7), (8, 361), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4d0) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 370) (RestInside.out (n := 370) f176 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 371) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 367), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4d3) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 372) (RestInside.exec (n := 372) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 367), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4d7) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f178 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 374) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 373), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4d9) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 375) (RestInside.out (n := 375) f179 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 376) (ρ' := [(0, 248), (1, 344), (2, 340), (3, 266), (4, 4), (5, 268), (6, 375), (7, 7), (8, 370), (9, 163), (10, 351), (11, 349), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a4dc) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_9 code

theorem rest_l10a26a_7 [Bindings] (code : CodeMap) :
    Rest (n := 310) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 308), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]
      119 0x10a452 bytes_l10a26a_7 b_l10a26a_7 := by
  have f140 : InstrSpec 0x10a452 [0x44, 0x88, 0x47, 0x17] (StorePre 0x10a452 4 (fun s => AddrMode.addr (.base 7 (.d8 0x17)) s (0x10a452 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a452 4 8 (.base 7 (.d8 0x17)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a452 4 8 (.base 7 (.d8 0x17))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a452 0x44 (by decide) 0 (.base 7 (.d8 0x17)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f141 : InstrSpec 0x10a456 [0x49, 0x89, 0xD8] (fun s => s.RIP = 0x10a456) (movR64R64Effect 0x10a456 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10a456 8 3).toInstrSpec (mov_r64_r64_effect_step 0x10a456 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x10a459 [0x88, 0x7F, 0x18] (StorePre 0x10a459 3 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10a459 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a459 3 7 (.base 7 (.d8 0x18)))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a459 3 7 (.base 7 (.d8 0x18))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a459 7 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f143 : InstrSpec 0x10a45c [0x41, 0x89, 0xDB] (fun s => s.RIP = 0x10a45c) (movR32R32Effect 0x10a45c 3 11 3)
      [.gpr 3] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x10a45c 3 11 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a45c 0x41 0xdb (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x10a45f [0x41, 0xC1, 0xEB, 0x18] (fun s => s.RIP = 0x10a45f) (shrR32Effect 0x10a45f 4 11 24)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a45f 4 11 24).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a45f 0x41 0xeb 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x10a463 [0x49, 0xC1, 0xEA, 0x28] (fun s => s.RIP = 0x10a463) (shrR64Effect 0x10a463 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a463 4 10 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a463 0x49 0xea 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f146 : InstrSpec 0x10a467 [0x49, 0xC1, 0xE8, 0x38] (fun s => s.RIP = 0x10a467) (shrR64Effect 0x10a467 4 8 56)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a467 4 8 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a467 0x49 0xe8 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f147 : InstrSpec 0x10a46b [0x44, 0x88, 0x5F, 0x19] (StorePre 0x10a46b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x19)) s (0x10a46b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a46b 4 11 (.base 7 (.d8 0x19)))
      [.gpr 11, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a46b 4 11 (.base 7 (.d8 0x19))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a46b 0x44 (by decide) 3 (.base 7 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f148 : InstrSpec 0x10a46f [0x49, 0x89, 0xCB] (fun s => s.RIP = 0x10a46f) (movR64R64Effect 0x10a46f 11 1)
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x10a46f 11 1).toInstrSpec (mov_r64_r64_effect_step 0x10a46f 0x49 0xcb (by decide) (by decide)) pre_rip
  have f149 : InstrSpec 0x10a472 [0x44, 0x88, 0x57, 0x1A] (StorePre 0x10a472 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1a)) s (0x10a472 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a472 4 10 (.base 7 (.d8 0x1a)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a472 4 10 (.base 7 (.d8 0x1a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a472 0x44 (by decide) 2 (.base 7 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f150 : InstrSpec 0x10a476 [0x49, 0x89, 0xCA] (fun s => s.RIP = 0x10a476) (movR64R64Effect 0x10a476 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10a476 10 1).toInstrSpec (mov_r64_r64_effect_step 0x10a476 0x49 0xca (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x10a479 [0x44, 0x88, 0x47, 0x1B] (StorePre 0x10a479 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1b)) s (0x10a479 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a479 4 8 (.base 7 (.d8 0x1b)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a479 4 8 (.base 7 (.d8 0x1b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a479 0x44 (by decide) 0 (.base 7 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f152 : InstrSpec 0x10a47d [0x88, 0x6F, 0x1C] (StorePre 0x10a47d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x10a47d + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a47d 3 5 (.base 7 (.d8 0x1c)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a47d 3 5 (.base 7 (.d8 0x1c))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a47d 5 (.base 7 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f153 : InstrSpec 0x10a480 [0x41, 0x89, 0xC8] (fun s => s.RIP = 0x10a480) (movR32R32Effect 0x10a480 3 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x10a480 3 8 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a480 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f154 : InstrSpec 0x10a483 [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x10a483) (movR64R64Effect 0x10a483 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a483 1 6).toInstrSpec (mov_r64_r64_effect_step 0x10a483 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x10a486 [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x10a486) (shrR64Effect 0x10a486 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a486 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x10a486 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x10a48a [0x48, 0x31, 0xD1] (fun s => s.RIP = 0x10a48a) (xorR64R64Effect 0x10a48a 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a48a 1 2).toInstrSpec (xor_r64_r64_effect_step 0x10a48a 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x10a48d [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x10a48d) (andR64R64Effect 0x10a48d 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a48d 1 9).toInstrSpec (and_r64_r64_effect_step 0x10a48d 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f158 : InstrSpec 0x10a490 [0x48, 0x31, 0xCA] (fun s => s.RIP = 0x10a490) (xorR64R64Effect 0x10a490 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a490 2 1).toInstrSpec (xor_r64_r64_effect_step 0x10a490 0x48 0xca (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x10a493 [0x48, 0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x10a493) (shlR64Effect 0x10a493 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a493 4 1 4).toInstrSpec (shl_r64_imm8_effect_step 0x10a493 0x48 0xe1 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 310) (RestInside.exec (n := 310) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 308), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a456) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f141 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 311), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a459) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.exec (n := 313) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 311), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a45c) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 314) (RestInside.out (n := 314) f143 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 315) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 311), (9, 163), (10, 292), (11, 314), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a45f) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f144 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 317) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 311), (9, 163), (10, 292), (11, 316), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a463) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f145 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 311), (9, 163), (10, 318), (11, 316), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a467) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f146 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 321) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 320), (9, 163), (10, 318), (11, 316), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a46b) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.exec (n := 322) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 320), (9, 163), (10, 318), (11, 316), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a46f) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f148 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 324) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 320), (9, 163), (10, 318), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a472) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 325) (RestInside.exec (n := 325) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 320), (9, 163), (10, 318), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a476) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f150 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 320), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a479) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.exec (n := 328) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 320), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a47d) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 329) (RestInside.exec (n := 329) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 320), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a480) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f153 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 330), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a483) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f154 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 248), (1, 332), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 330), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a486) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f155 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 335) (ρ' := [(0, 248), (1, 334), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 330), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a48a) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f156 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 248), (1, 336), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 330), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a48d) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f157 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 339) (ρ' := [(0, 248), (1, 338), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 330), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a490) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 340) (RestInside.out (n := 340) f158 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 341) (ρ' := [(0, 248), (1, 338), (2, 340), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 330), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a493) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.out (n := 342) f159 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 343) (ρ' := [(0, 248), (1, 342), (2, 340), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 330), (9, 163), (10, 326), (11, 323), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a497) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_8 code

theorem rest_l10a26a_6 [Bindings] (code : CodeMap) :
    Rest (n := 278) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 276), (9, 163), (10, 271), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]
      139 0x10a40a bytes_l10a26a_6 b_l10a26a_6 := by
  have f120 : InstrSpec 0x10a40a [0x41, 0xC1, 0xE8, 0x10] (fun s => s.RIP = 0x10a40a) (shrR32Effect 0x10a40a 4 8 16)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a40a 4 8 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a40a 0x41 0xe8 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x10a40e [0x44, 0x88, 0x67, 0x0F] (StorePre 0x10a40e 4 (fun s => AddrMode.addr (.base 7 (.d8 0xf)) s (0x10a40e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a40e 4 12 (.base 7 (.d8 0xf)))
      [.gpr 12, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a40e 4 12 (.base 7 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a40e 0x44 (by decide) 4 (.base 7 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f122 : InstrSpec 0x10a412 [0x49, 0x89, 0xDA] (fun s => s.RIP = 0x10a412) (movR64R64Effect 0x10a412 10 3)
      [.gpr 3] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10a412 10 3).toInstrSpec (mov_r64_r64_effect_step 0x10a412 0x49 0xda (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x10a415 [0x49, 0xC1, 0xEA, 0x20] (fun s => s.RIP = 0x10a415) (shrR64Effect 0x10a415 4 10 32)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a415 4 10 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a415 0x49 0xea 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x10a419 [0x88, 0x5F, 0x10] (StorePre 0x10a419 3 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10a419 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a419 3 3 (.base 7 (.d8 0x10)))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a419 3 3 (.base 7 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x10a419 3 (by decide) (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f125 : InstrSpec 0x10a41c [0x44, 0x88, 0x47, 0x11] (StorePre 0x10a41c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x11)) s (0x10a41c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a41c 4 8 (.base 7 (.d8 0x11)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a41c 4 8 (.base 7 (.d8 0x11))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a41c 0x44 (by decide) 0 (.base 7 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f126 : InstrSpec 0x10a420 [0x49, 0x89, 0xD8] (fun s => s.RIP = 0x10a420) (movR64R64Effect 0x10a420 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10a420 8 3).toInstrSpec (mov_r64_r64_effect_step 0x10a420 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x10a423 [0x49, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x10a423) (shrR64Effect 0x10a423 4 8 48)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a423 4 8 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a423 0x49 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x10a427 [0x44, 0x88, 0x57, 0x12] (StorePre 0x10a427 4 (fun s => AddrMode.addr (.base 7 (.d8 0x12)) s (0x10a427 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a427 4 10 (.base 7 (.d8 0x12)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a427 4 10 (.base 7 (.d8 0x12))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a427 0x44 (by decide) 2 (.base 7 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f129 : InstrSpec 0x10a42b [0x49, 0x89, 0xDA] (fun s => s.RIP = 0x10a42b) (movR64R64Effect 0x10a42b 10 3)
      [.gpr 3] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10a42b 10 3).toInstrSpec (mov_r64_r64_effect_step 0x10a42b 0x49 0xda (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x10a42e [0x44, 0x88, 0x47, 0x13] (StorePre 0x10a42e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x13)) s (0x10a42e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a42e 4 8 (.base 7 (.d8 0x13)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a42e 4 8 (.base 7 (.d8 0x13))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a42e 0x44 (by decide) 0 (.base 7 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f131 : InstrSpec 0x10a432 [0x41, 0x89, 0xC8] (fun s => s.RIP = 0x10a432) (movR32R32Effect 0x10a432 3 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x10a432 3 8 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a432 0x41 0xc8 (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x10a435 [0x41, 0xC1, 0xE8, 0x10] (fun s => s.RIP = 0x10a435) (shrR32Effect 0x10a435 4 8 16)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a435 4 8 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a435 0x41 0xe8 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x10a439 [0x88, 0x4F, 0x14] (StorePre 0x10a439 3 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x10a439 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a439 3 1 (.base 7 (.d8 0x14)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a439 3 1 (.base 7 (.d8 0x14))).toInstrSpec (mov_m8_r8_effect_step 0x10a439 1 (by decide) (.base 7 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f134 : InstrSpec 0x10a43c [0x44, 0x88, 0x47, 0x15] (StorePre 0x10a43c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x15)) s (0x10a43c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a43c 4 8 (.base 7 (.d8 0x15)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a43c 4 8 (.base 7 (.d8 0x15))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a43c 0x44 (by decide) 0 (.base 7 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f135 : InstrSpec 0x10a440 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x10a440) (movR64R64Effect 0x10a440 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10a440 8 1).toInstrSpec (mov_r64_r64_effect_step 0x10a440 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x10a443 [0x49, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x10a443) (shrR64Effect 0x10a443 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a443 4 8 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a443 0x49 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x10a447 [0x44, 0x88, 0x47, 0x16] (StorePre 0x10a447 4 (fun s => AddrMode.addr (.base 7 (.d8 0x16)) s (0x10a447 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a447 4 8 (.base 7 (.d8 0x16)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a447 4 8 (.base 7 (.d8 0x16))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a447 0x44 (by decide) 0 (.base 7 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f138 : InstrSpec 0x10a44b [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x10a44b) (movR64R64Effect 0x10a44b 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x10a44b 8 1).toInstrSpec (mov_r64_r64_effect_step 0x10a44b 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f139 : InstrSpec 0x10a44e [0x49, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x10a44e) (shrR64Effect 0x10a44e 4 8 48)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a44e 4 8 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a44e 0x49 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f120 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 278), (9, 163), (10, 271), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a40e) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.exec (n := 280) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 278), (9, 163), (10, 271), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a412) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 281) (RestInside.out (n := 281) f122 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 282) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 278), (9, 163), (10, 281), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a415) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f123 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 278), (9, 163), (10, 283), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a419) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.exec (n := 285) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 278), (9, 163), (10, 283), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a41c) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 286) (RestInside.exec (n := 286) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 278), (9, 163), (10, 283), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a420) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f126 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 287), (9, 163), (10, 283), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a423) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f127 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 289), (9, 163), (10, 283), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a427) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.exec (n := 291) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 289), (9, 163), (10, 283), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a42b) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f129 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 289), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a42e) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.exec (n := 294) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 289), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a432) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f131 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 295), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a435) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f132 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 297), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a439) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.exec (n := 299) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 297), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a43c) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 300) (RestInside.exec (n := 300) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 297), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a440) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 301) (RestInside.out (n := 301) f135 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 302) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 301), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a443) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 303) (RestInside.out (n := 303) f136 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 304) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 303), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a447) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 305) (RestInside.exec (n := 305) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 303), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a44b) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f138 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 306), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a44e) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.out (n := 308) f139 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 309) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 308), (9, 163), (10, 292), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a452) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_7 code

theorem rest_l10a26a_5 [Bindings] (code : CodeMap) :
    Rest (n := 240) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]
      159 0x10a3c6 bytes_l10a26a_5 b_l10a26a_5 := by
  have f100 : InstrSpec 0x10a3c6 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x10a3c6) (movR64R64Effect 0x10a3c6 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a3c6 1 8).toInstrSpec (mov_r64_r64_effect_step 0x10a3c6 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x10a3c9 [0x48, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10a3c9) (shrR64Effect 0x10a3c9 4 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3c9 4 1 2).toInstrSpec (shr_r64_imm8_effect_step 0x10a3c9 0x48 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x10a3cd [0x48, 0x31, 0xC1] (fun s => s.RIP = 0x10a3cd) (xorR64R64Effect 0x10a3cd 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a3cd 1 0).toInstrSpec (xor_r64_r64_effect_step 0x10a3cd 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x10a3d0 [0x4C, 0x21, 0xD9] (fun s => s.RIP = 0x10a3d0) (andR64R64Effect 0x10a3d0 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a3d0 1 11).toInstrSpec (and_r64_r64_effect_step 0x10a3d0 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x10a3d3 [0x48, 0x31, 0xC8] (fun s => s.RIP = 0x10a3d3) (xorR64R64Effect 0x10a3d3 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a3d3 0 1).toInstrSpec (xor_r64_r64_effect_step 0x10a3d3 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x10a3d6 [0x48, 0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10a3d6) (shlR64Effect 0x10a3d6 4 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a3d6 4 1 2).toInstrSpec (shl_r64_imm8_effect_step 0x10a3d6 0x48 0xe1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x10a3da [0x4C, 0x31, 0xC1] (fun s => s.RIP = 0x10a3da) (xorR64R64Effect 0x10a3da 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a3da 1 8).toInstrSpec (xor_r64_r64_effect_step 0x10a3da 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x10a3dd [0x4C, 0x89, 0xFB] (fun s => s.RIP = 0x10a3dd) (movR64R64Effect 0x10a3dd 3 15)
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10a3dd 3 15).toInstrSpec (mov_r64_r64_effect_step 0x10a3dd 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x10a3e0 [0x48, 0xC1, 0xEB, 0x04] (fun s => s.RIP = 0x10a3e0) (shrR64Effect 0x10a3e0 4 3 4)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3e0 4 3 4).toInstrSpec (shr_r64_imm8_effect_step 0x10a3e0 0x48 0xeb 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x10a3e4 [0x48, 0x31, 0xCB] (fun s => s.RIP = 0x10a3e4) (xorR64R64Effect 0x10a3e4 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a3e4 3 1).toInstrSpec (xor_r64_r64_effect_step 0x10a3e4 0x48 0xcb (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x10a3e7 [0x4C, 0x21, 0xCB] (fun s => s.RIP = 0x10a3e7) (andR64R64Effect 0x10a3e7 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a3e7 3 9).toInstrSpec (and_r64_r64_effect_step 0x10a3e7 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x10a3ea [0x48, 0x31, 0xD9] (fun s => s.RIP = 0x10a3ea) (xorR64R64Effect 0x10a3ea 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a3ea 1 3).toInstrSpec (xor_r64_r64_effect_step 0x10a3ea 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x10a3ed [0x48, 0xC1, 0xE3, 0x04] (fun s => s.RIP = 0x10a3ed) (shlR64Effect 0x10a3ed 4 3 4)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a3ed 4 3 4).toInstrSpec (shl_r64_imm8_effect_step 0x10a3ed 0x48 0xe3 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x10a3f1 [0x4C, 0x31, 0xFB] (fun s => s.RIP = 0x10a3f1) (xorR64R64Effect 0x10a3f1 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a3f1 3 15).toInstrSpec (xor_r64_r64_effect_step 0x10a3f1 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x10a3f4 [0xC1, 0xED, 0x18] (fun s => s.RIP = 0x10a3f4) (shrR32Effect 0x10a3f4 3 5 24)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a3f4 3 5 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a3f4 0xed 0x18 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x10a3f7 [0x40, 0x88, 0x6F, 0x0D] (StorePre 0x10a3f7 4 (fun s => AddrMode.addr (.base 7 (.d8 0xd)) s (0x10a3f7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a3f7 4 5 (.base 7 (.d8 0xd)))
      [.gpr 5, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3f7 4 5 (.base 7 (.d8 0xd))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a3f7 0x40 (by decide) 5 (.base 7 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f116 : InstrSpec 0x10a3fb [0x49, 0xC1, 0xEA, 0x28] (fun s => s.RIP = 0x10a3fb) (shrR64Effect 0x10a3fb 4 10 40)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3fb 4 10 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a3fb 0x49 0xea 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x10a3ff [0x49, 0xC1, 0xEC, 0x38] (fun s => s.RIP = 0x10a3ff) (shrR64Effect 0x10a3ff 4 12 56)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3ff 4 12 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a3ff 0x49 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x10a403 [0x44, 0x88, 0x57, 0x0E] (StorePre 0x10a403 4 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x10a403 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a403 4 10 (.base 7 (.d8 0xe)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a403 4 10 (.base 7 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a403 0x44 (by decide) 2 (.base 7 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f119 : InstrSpec 0x10a407 [0x41, 0x89, 0xD8] (fun s => s.RIP = 0x10a407) (movR32R32Effect 0x10a407 3 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x10a407 3 8 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a407 0x41 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f100 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 121), (1, 240), (2, 151), (3, 167), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3c9) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f101 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 121), (1, 242), (2, 151), (3, 167), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3cd) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f102 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 121), (1, 244), (2, 151), (3, 167), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3d0) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f103 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 121), (1, 246), (2, 151), (3, 167), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3d3) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.out (n := 248) f104 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 249) (ρ' := [(0, 248), (1, 246), (2, 151), (3, 167), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3d6) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f105 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 248), (1, 250), (2, 151), (3, 167), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3da) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f106 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 248), (1, 252), (2, 151), (3, 167), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3dd) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f107 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 248), (1, 252), (2, 151), (3, 254), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3e0) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f108 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 257) (ρ' := [(0, 248), (1, 252), (2, 151), (3, 256), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3e4) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.out (n := 258) f109 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 259) (ρ' := [(0, 248), (1, 252), (2, 151), (3, 258), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3e7) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 260) (RestInside.out (n := 260) f110 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 261) (ρ' := [(0, 248), (1, 252), (2, 151), (3, 260), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ea) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f111 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 260), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ed) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f112 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 264), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3f1) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f113 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3f4) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f114 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3f7) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.exec (n := 270) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3fb) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 271) (RestInside.out (n := 271) f116 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 272) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 107), (9, 163), (10, 271), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ff) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f117 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 107), (9, 163), (10, 271), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a403) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.exec (n := 275) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 107), (9, 163), (10, 271), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a407) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f119 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 248), (1, 262), (2, 151), (3, 266), (4, 4), (5, 268), (6, 137), (7, 7), (8, 276), (9, 163), (10, 271), (11, 133), (12, 273), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a40a) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_6 code

theorem rest_l10a26a_4 [Bindings] (code : CodeMap) :
    Rest (n := 206) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 204), (22, 22), (39, 39), (50, 50), (51, 51)]
      179 0x10a383 bytes_l10a26a_4 b_l10a26a_4 := by
  have f80 : InstrSpec 0x10a383 [0x49, 0xC1, 0xEF, 0x30] (fun s => s.RIP = 0x10a383) (shrR64Effect 0x10a383 4 15 48)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a383 4 15 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a383 0x49 0xef 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x10a387 [0x44, 0x88, 0x7F, 0x07] (StorePre 0x10a387 4 (fun s => AddrMode.addr (.base 7 (.d8 0x7)) s (0x10a387 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a387 4 15 (.base 7 (.d8 0x7)))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a387 4 15 (.base 7 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a387 0x44 (by decide) 7 (.base 7 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f82 : InstrSpec 0x10a38b [0x88, 0x6F, 0x08] (StorePre 0x10a38b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10a38b + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a38b 3 5 (.base 7 (.d8 0x8)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a38b 3 5 (.base 7 (.d8 0x8))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a38b 5 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f83 : InstrSpec 0x10a38e [0x4D, 0x89, 0xD7] (fun s => s.RIP = 0x10a38e) (movR64R64Effect 0x10a38e 15 10)
      [.gpr 10] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10a38e 15 10).toInstrSpec (mov_r64_r64_effect_step 0x10a38e 0x4d 0xd7 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x10a391 [0x49, 0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x10a391) (shrR64Effect 0x10a391 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a391 4 15 2).toInstrSpec (shr_r64_imm8_effect_step 0x10a391 0x49 0xef 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x10a395 [0x4D, 0x31, 0xF7] (fun s => s.RIP = 0x10a395) (xorR64R64Effect 0x10a395 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a395 15 14).toInstrSpec (xor_r64_r64_effect_step 0x10a395 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x10a398 [0x4D, 0x21, 0xDF] (fun s => s.RIP = 0x10a398) (andR64R64Effect 0x10a398 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a398 15 11).toInstrSpec (and_r64_r64_effect_step 0x10a398 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x10a39b [0x4D, 0x31, 0xFE] (fun s => s.RIP = 0x10a39b) (xorR64R64Effect 0x10a39b 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a39b 14 15).toInstrSpec (xor_r64_r64_effect_step 0x10a39b 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x10a39e [0x49, 0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x10a39e) (shlR64Effect 0x10a39e 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a39e 4 15 2).toInstrSpec (shl_r64_imm8_effect_step 0x10a39e 0x49 0xe7 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x10a3a2 [0x4D, 0x31, 0xD7] (fun s => s.RIP = 0x10a3a2) (xorR64R64Effect 0x10a3a2 15 10)
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a3a2 15 10).toInstrSpec (xor_r64_r64_effect_step 0x10a3a2 0x4d 0xd7 (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x10a3a5 [0xC1, 0xE9, 0x18] (fun s => s.RIP = 0x10a3a5) (shrR32Effect 0x10a3a5 3 1 24)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a3a5 3 1 24).toInstrSpec (shr_r32_imm8_effect_step 0x10a3a5 0xe9 0x18 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x10a3a8 [0x49, 0xC1, 0xED, 0x28] (fun s => s.RIP = 0x10a3a8) (shrR64Effect 0x10a3a8 4 13 40)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3a8 4 13 40).toInstrSpec (shr_r64_imm8_effect_step 0x10a3a8 0x49 0xed 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x10a3ac [0x48, 0xC1, 0xED, 0x38] (fun s => s.RIP = 0x10a3ac) (shrR64Effect 0x10a3ac 4 5 56)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a3ac 4 5 56).toInstrSpec (shr_r64_imm8_effect_step 0x10a3ac 0x48 0xed 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x10a3b0 [0x88, 0x4F, 0x09] (StorePre 0x10a3b0 3 (fun s => AddrMode.addr (.base 7 (.d8 0x9)) s (0x10a3b0 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3b0 3 1 (.base 7 (.d8 0x9)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3b0 3 1 (.base 7 (.d8 0x9))).toInstrSpec (mov_m8_r8_effect_step 0x10a3b0 1 (by decide) (.base 7 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f94 : InstrSpec 0x10a3b3 [0x49, 0x89, 0xDA] (fun s => s.RIP = 0x10a3b3) (movR64R64Effect 0x10a3b3 10 3)
      [.gpr 3] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x10a3b3 10 3).toInstrSpec (mov_r64_r64_effect_step 0x10a3b3 0x49 0xda (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x10a3b6 [0x44, 0x88, 0x6F, 0x0A] (StorePre 0x10a3b6 4 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x10a3b6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a3b6 4 13 (.base 7 (.d8 0xa)))
      [.gpr 13, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3b6 4 13 (.base 7 (.d8 0xa))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a3b6 0x44 (by decide) 5 (.base 7 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x10a3ba [0x49, 0x89, 0xDC] (fun s => s.RIP = 0x10a3ba) (movR64R64Effect 0x10a3ba 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10a3ba 12 3).toInstrSpec (mov_r64_r64_effect_step 0x10a3ba 0x49 0xdc (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x10a3bd [0x40, 0x88, 0x6F, 0x0B] (StorePre 0x10a3bd 4 (fun s => AddrMode.addr (.base 7 (.d8 0xb)) s (0x10a3bd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a3bd 4 5 (.base 7 (.d8 0xb)))
      [.gpr 5, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a3bd 4 5 (.base 7 (.d8 0xb))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a3bd 0x40 (by decide) 5 (.base 7 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f98 : InstrSpec 0x10a3c1 [0x88, 0x7F, 0x0C] (StorePre 0x10a3c1 3 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x10a3c1 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a3c1 3 7 (.base 7 (.d8 0xc)))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM8R8NoRexEffect_footprint 0x10a3c1 3 7 (.base 7 (.d8 0xc))).toInstrSpec (mov_m8_r8_norex_effect_step 0x10a3c1 7 (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f99 : InstrSpec 0x10a3c4 [0x89, 0xDD] (fun s => s.RIP = 0x10a3c4) (movR32R32Effect 0x10a3c4 2 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x10a3c4 2 5 3).toInstrSpec (mov_r32_r32_effect_step 0x10a3c4 0xdd (by decide)) pre_rip
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f80 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 206), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a387) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.exec (n := 208) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 206), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a38b) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 209) (RestInside.exec (n := 209) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 206), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a38e) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f83 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 210), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a391) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f84 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 212), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a395) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f85 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 214), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a398) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f86 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 216), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a39b) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f87 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 218), (15, 216), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a39e) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f88 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 218), (15, 220), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3a2) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f89 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3a5) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f90 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3a8) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f91 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ac) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f92 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 229) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 228), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3b0) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.exec (n := 230) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 228), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3b3) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f94 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 228), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 183), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3b6) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.exec (n := 233) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 228), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 183), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3ba) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f96 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 228), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3bd) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.exec (n := 236) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 228), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3c1) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 237) (RestInside.exec (n := 237) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 228), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3c4) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f99 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 121), (1, 224), (2, 151), (3, 167), (4, 4), (5, 238), (6, 137), (7, 7), (8, 107), (9, 163), (10, 231), (11, 133), (12, 234), (13, 226), (14, 218), (15, 222), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a3c6) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_5 code

theorem rest_l10a26a_3 [Bindings] (code : CodeMap) :
    Rest (n := 173) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]
      199 0x10a340 bytes_l10a26a_3 b_l10a26a_3 := by
  have f60 : InstrSpec 0x10a340 [0x89, 0xCD] (fun s => s.RIP = 0x10a340) (movR32R32Effect 0x10a340 2 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x10a340 2 5 1).toInstrSpec (mov_r32_r32_effect_step 0x10a340 0xcd (by decide)) pre_rip
  have f61 : InstrSpec 0x10a342 [0xC1, 0xED, 0x10] (fun s => s.RIP = 0x10a342) (shrR32Effect 0x10a342 3 5 16)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a342 3 5 16).toInstrSpec (shr_r32_imm8_effect_step 0x10a342 0xed 0x10 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x10a345 [0x49, 0x89, 0xCF] (fun s => s.RIP = 0x10a345) (movR64R64Effect 0x10a345 15 1)
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10a345 15 1).toInstrSpec (mov_r64_r64_effect_step 0x10a345 0x49 0xcf (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x10a348 [0x49, 0xC1, 0xEF, 0x20] (fun s => s.RIP = 0x10a348) (shrR64Effect 0x10a348 4 15 32)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a348 4 15 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a348 0x49 0xef 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x10a34c [0x49, 0x89, 0xCC] (fun s => s.RIP = 0x10a34c) (movR64R64Effect 0x10a34c 12 1)
      [.gpr 1] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10a34c 12 1).toInstrSpec (mov_r64_r64_effect_step 0x10a34c 0x49 0xcc (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x10a34f [0x49, 0xC1, 0xEC, 0x30] (fun s => s.RIP = 0x10a34f) (shrR64Effect 0x10a34f 4 12 48)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a34f 4 12 48).toInstrSpec (shr_r64_imm8_effect_step 0x10a34f 0x49 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x10a353 [0x88, 0x0F] (StorePre 0x10a353 2 (fun s => AddrMode.addr (.base 7 .none) s (0x10a353 + BitVec.ofNat 64 2)) 1) (movM8R8Effect 0x10a353 2 1 (.base 7 .none))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a353 2 1 (.base 7 .none)).toInstrSpec (mov_m8_r8_effect_step 0x10a353 1 (by decide) (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x10a355 [0x40, 0x88, 0x6F, 0x01] (StorePre 0x10a355 4 (fun s => AddrMode.addr (.base 7 (.d8 0x1)) s (0x10a355 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a355 4 5 (.base 7 (.d8 0x1)))
      [.gpr 5, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a355 4 5 (.base 7 (.d8 0x1))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a355 0x40 (by decide) 5 (.base 7 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x10a359 [0x49, 0x89, 0xCD] (fun s => s.RIP = 0x10a359) (movR64R64Effect 0x10a359 13 1)
      [.gpr 1] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10a359 13 1).toInstrSpec (mov_r64_r64_effect_step 0x10a359 0x49 0xcd (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x10a35c [0x44, 0x88, 0x7F, 0x02] (StorePre 0x10a35c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x10a35c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a35c 4 15 (.base 7 (.d8 0x2)))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a35c 4 15 (.base 7 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a35c 0x44 (by decide) 7 (.base 7 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x10a360 [0x48, 0x89, 0xCD] (fun s => s.RIP = 0x10a360) (movR64R64Effect 0x10a360 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x10a360 5 1).toInstrSpec (mov_r64_r64_effect_step 0x10a360 0x48 0xcd (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x10a363 [0x44, 0x88, 0x67, 0x03] (StorePre 0x10a363 4 (fun s => AddrMode.addr (.base 7 (.d8 0x3)) s (0x10a363 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a363 4 12 (.base 7 (.d8 0x3)))
      [.gpr 12, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a363 4 12 (.base 7 (.d8 0x3))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a363 0x44 (by decide) 4 (.base 7 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x10a367 [0x41, 0x89, 0xDF] (fun s => s.RIP = 0x10a367) (movR32R32Effect 0x10a367 3 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x10a367 3 15 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a367 0x41 0xdf (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x10a36a [0x41, 0xC1, 0xEF, 0x10] (fun s => s.RIP = 0x10a36a) (shrR32Effect 0x10a36a 4 15 16)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a36a 4 15 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a36a 0x41 0xef 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10a36e [0x88, 0x5F, 0x04] (StorePre 0x10a36e 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x10a36e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a36e 3 3 (.base 7 (.d8 0x4)))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a36e 3 3 (.base 7 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x10a36e 3 (by decide) (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x10a371 [0x44, 0x88, 0x7F, 0x05] (StorePre 0x10a371 4 (fun s => AddrMode.addr (.base 7 (.d8 0x5)) s (0x10a371 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a371 4 15 (.base 7 (.d8 0x5)))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a371 4 15 (.base 7 (.d8 0x5))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a371 0x44 (by decide) 7 (.base 7 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x10a375 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x10a375) (movR64R64Effect 0x10a375 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10a375 15 3).toInstrSpec (mov_r64_r64_effect_step 0x10a375 0x49 0xdf (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x10a378 [0x49, 0xC1, 0xEF, 0x20] (fun s => s.RIP = 0x10a378) (shrR64Effect 0x10a378 4 15 32)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a378 4 15 32).toInstrSpec (shr_r64_imm8_effect_step 0x10a378 0x49 0xef 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x10a37c [0x44, 0x88, 0x7F, 0x06] (StorePre 0x10a37c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x10a37c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a37c 4 15 (.base 7 (.d8 0x6)))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a37c 4 15 (.base 7 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10a37c 0x44 (by decide) 7 (.base 7 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f79 : InstrSpec 0x10a380 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x10a380) (movR64R64Effect 0x10a380 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10a380 15 3).toInstrSpec (mov_r64_r64_effect_step 0x10a380 0x49 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f60 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 173), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a342) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f61 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 175), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a345) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f62 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 175), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 177), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a348) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f63 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 175), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a34c) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f64 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 175), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 181), (14, 93), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a34f) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f65 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 175), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (14, 93), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a353) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.exec (n := 185) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 175), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (14, 93), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a355) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 175), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (14, 93), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a359) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f68 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 175), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a35c) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.exec (n := 189) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 175), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a360) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f70 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a363) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.exec (n := 192) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a367) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 193), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a36a) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f73 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 195), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a36e) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.exec (n := 197) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 195), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a371) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 198) (RestInside.exec (n := 198) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 195), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a375) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f76 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 199), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a378) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f77 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 201), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a37c) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.exec (n := 203) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 201), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a380) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f79 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (5, 190), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (12, 183), (13, 187), (14, 93), (15, 204), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a383) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_4 code

theorem rest_l10a26a_2 [Bindings] (code : CodeMap) :
    Rest (n := 133) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 131), (22, 22), (39, 39), (50, 50), (51, 51)]
      219 0x10a2f1 bytes_l10a26a_2 b_l10a26a_2 := by
  have f40 : InstrSpec 0x10a2f1 [0x49, 0xBB, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33] (fun s => s.RIP = 0x10a2f1) (movR64Imm64Effect 0x10a2f1 11 0x3333333333333333)
      [] [] [.reg 11, .rip] :=
    (movR64Imm64Effect_footprint 0x10a2f1 11 0x3333333333333333).toInstrSpec (mov_r64_imm64_effect_step 0x10a2f1 0x49 0xbb (by decide) (by decide) 0x3333333333333333) pre_rip
  have f41 : InstrSpec 0x10a2fb [0x4D, 0x21, 0xDF] (fun s => s.RIP = 0x10a2fb) (andR64R64Effect 0x10a2fb 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a2fb 15 11).toInstrSpec (and_r64_r64_effect_step 0x10a2fb 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x10a2fe [0x4C, 0x31, 0xFE] (fun s => s.RIP = 0x10a2fe) (xorR64R64Effect 0x10a2fe 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2fe 6 15).toInstrSpec (xor_r64_r64_effect_step 0x10a2fe 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x10a301 [0x49, 0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x10a301) (shlR64Effect 0x10a301 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a301 4 15 2).toInstrSpec (shl_r64_imm8_effect_step 0x10a301 0x49 0xe7 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x10a305 [0x49, 0x31, 0xCF] (fun s => s.RIP = 0x10a305) (xorR64R64Effect 0x10a305 15 1)
      [.gpr 15, .gpr 1] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a305 15 1).toInstrSpec (xor_r64_r64_effect_step 0x10a305 0x49 0xcf (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10a308 [0x4C, 0x89, 0xCB] (fun s => s.RIP = 0x10a308) (movR64R64Effect 0x10a308 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10a308 3 9).toInstrSpec (mov_r64_r64_effect_step 0x10a308 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10a30b [0x48, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x10a30b) (shrR64Effect 0x10a30b 4 3 2)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a30b 4 3 2).toInstrSpec (shr_r64_imm8_effect_step 0x10a30b 0x48 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10a30f [0x48, 0x31, 0xD3] (fun s => s.RIP = 0x10a30f) (xorR64R64Effect 0x10a30f 3 2)
      [.gpr 3, .gpr 2] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a30f 3 2).toInstrSpec (xor_r64_r64_effect_step 0x10a30f 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10a312 [0x4C, 0x21, 0xDB] (fun s => s.RIP = 0x10a312) (andR64R64Effect 0x10a312 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a312 3 11).toInstrSpec (and_r64_r64_effect_step 0x10a312 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x10a315 [0x48, 0x31, 0xDA] (fun s => s.RIP = 0x10a315) (xorR64R64Effect 0x10a315 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a315 2 3).toInstrSpec (xor_r64_r64_effect_step 0x10a315 0x48 0xda (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x10a318 [0x48, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x10a318) (shlR64Effect 0x10a318 4 3 2)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a318 4 3 2).toInstrSpec (shl_r64_imm8_effect_step 0x10a318 0x48 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x10a31c [0x4C, 0x31, 0xCB] (fun s => s.RIP = 0x10a31c) (xorR64R64Effect 0x10a31c 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a31c 3 9).toInstrSpec (xor_r64_r64_effect_step 0x10a31c 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10a31f [0x4C, 0x89, 0xF9] (fun s => s.RIP = 0x10a31f) (movR64R64Effect 0x10a31f 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a31f 1 15).toInstrSpec (mov_r64_r64_effect_step 0x10a31f 0x4c 0xf9 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10a322 [0x48, 0xC1, 0xE9, 0x04] (fun s => s.RIP = 0x10a322) (shrR64Effect 0x10a322 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a322 4 1 4).toInstrSpec (shr_r64_imm8_effect_step 0x10a322 0x48 0xe9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x10a326 [0x48, 0x31, 0xD9] (fun s => s.RIP = 0x10a326) (xorR64R64Effect 0x10a326 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a326 1 3).toInstrSpec (xor_r64_r64_effect_step 0x10a326 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10a329 [0x49, 0xB9, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F] (fun s => s.RIP = 0x10a329) (movR64Imm64Effect 0x10a329 9 0xf0f0f0f0f0f0f0f)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x10a329 9 0xf0f0f0f0f0f0f0f).toInstrSpec (mov_r64_imm64_effect_step 0x10a329 0x49 0xb9 (by decide) (by decide) 0xf0f0f0f0f0f0f0f) pre_rip
  have f56 : InstrSpec 0x10a333 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x10a333) (andR64R64Effect 0x10a333 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a333 1 9).toInstrSpec (and_r64_r64_effect_step 0x10a333 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x10a336 [0x48, 0x31, 0xCB] (fun s => s.RIP = 0x10a336) (xorR64R64Effect 0x10a336 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a336 3 1).toInstrSpec (xor_r64_r64_effect_step 0x10a336 0x48 0xcb (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x10a339 [0x48, 0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x10a339) (shlR64Effect 0x10a339 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x10a339 4 1 4).toInstrSpec (shl_r64_imm8_effect_step 0x10a339 0x48 0xe1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10a33d [0x4C, 0x31, 0xF9] (fun s => s.RIP = 0x10a33d) (xorR64R64Effect 0x10a33d 1 15)
      [.gpr 1, .gpr 15] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a33d 1 15).toInstrSpec (xor_r64_r64_effect_step 0x10a33d 0x4c 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f40 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 131), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2fb) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f41 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 135), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2fe) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f42 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 135), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a301) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f43 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 139), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a305) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a308) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f45 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 143), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a30b) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f46 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 145), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a30f) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f47 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 147), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a312) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f48 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 149), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a315) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f49 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 121), (1, 83), (2, 151), (3, 149), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a318) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f50 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 121), (1, 83), (2, 151), (3, 153), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a31c) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f51 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 121), (1, 83), (2, 151), (3, 155), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a31f) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f52 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 121), (1, 157), (2, 151), (3, 155), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a322) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f53 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 121), (1, 159), (2, 151), (3, 155), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a326) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f54 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 121), (1, 161), (2, 151), (3, 155), (4, 4), (6, 137), (7, 7), (8, 107), (9, 111), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a329) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f55 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 121), (1, 161), (2, 151), (3, 155), (4, 4), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a333) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f56 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 121), (1, 165), (2, 151), (3, 155), (4, 4), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a336) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f57 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 121), (1, 165), (2, 151), (3, 167), (4, 4), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a339) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 121), (1, 169), (2, 151), (3, 167), (4, 4), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a33d) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 121), (1, 171), (2, 151), (3, 167), (4, 4), (6, 137), (7, 7), (8, 107), (9, 163), (10, 79), (11, 133), (14, 93), (15, 141), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a340) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_3 code

theorem rest_l10a26a_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x10a26a bytes_l10a26a) [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 91), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]
      239 0x10a2b4 bytes_l10a26a_1 b_l10a26a_1 := by
  have f20 : InstrSpec 0x10a2b4 [0x49, 0x31, 0xF6] (fun s => s.RIP = 0x10a2b4) (xorR64R64Effect 0x10a2b4 14 6)
      [.gpr 14, .gpr 6] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2b4 14 6).toInstrSpec (xor_r64_r64_effect_step 0x10a2b4 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10a2b7 [0x48, 0x01, 0xF6] (fun s => s.RIP = 0x10a2b7) (addR64R64Effect 0x10a2b7 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a2b7 6 6).toInstrSpec (add_r64_r64_effect_step 0x10a2b7 0x48 0xf6 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10a2ba [0x4C, 0x31, 0xFE] (fun s => s.RIP = 0x10a2ba) (xorR64R64Effect 0x10a2ba 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2ba 6 15).toInstrSpec (xor_r64_r64_effect_step 0x10a2ba 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10a2bd [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x10a2bd) (movR64R64Effect 0x10a2bd 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10a2bd 9 2).toInstrSpec (mov_r64_r64_effect_step 0x10a2bd 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x10a2c0 [0x49, 0xD1, 0xE9] (fun s => s.RIP = 0x10a2c0) (shrR64Effect 0x10a2c0 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a2c0 3 9 1).toInstrSpec (shr_r64_one_effect_step 0x10a2c0 0x49 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10a2c3 [0x4D, 0x31, 0xC1] (fun s => s.RIP = 0x10a2c3) (xorR64R64Effect 0x10a2c3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2c3 9 8).toInstrSpec (xor_r64_r64_effect_step 0x10a2c3 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10a2c6 [0x49, 0x21, 0xD9] (fun s => s.RIP = 0x10a2c6) (andR64R64Effect 0x10a2c6 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a2c6 9 3).toInstrSpec (and_r64_r64_effect_step 0x10a2c6 0x49 0xd9 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10a2c9 [0x4D, 0x31, 0xC8] (fun s => s.RIP = 0x10a2c9) (xorR64R64Effect 0x10a2c9 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2c9 8 9).toInstrSpec (xor_r64_r64_effect_step 0x10a2c9 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10a2cc [0x4D, 0x01, 0xC9] (fun s => s.RIP = 0x10a2cc) (addR64R64Effect 0x10a2cc 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a2cc 9 9).toInstrSpec (add_r64_r64_effect_step 0x10a2cc 0x4d 0xc9 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10a2cf [0x49, 0x31, 0xD1] (fun s => s.RIP = 0x10a2cf) (xorR64R64Effect 0x10a2cf 9 2)
      [.gpr 9, .gpr 2] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2cf 9 2).toInstrSpec (xor_r64_r64_effect_step 0x10a2cf 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10a2d2 [0x4C, 0x89, 0xDA] (fun s => s.RIP = 0x10a2d2) (movR64R64Effect 0x10a2d2 2 11)
      [.gpr 11] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a2d2 2 11).toInstrSpec (mov_r64_r64_effect_step 0x10a2d2 0x4c 0xda (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10a2d5 [0x48, 0xD1, 0xEA] (fun s => s.RIP = 0x10a2d5) (shrR64Effect 0x10a2d5 3 2 1)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a2d5 3 2 1).toInstrSpec (shr_r64_one_effect_step 0x10a2d5 0x48 0xea (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10a2d8 [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x10a2d8) (xorR64R64Effect 0x10a2d8 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2d8 2 0).toInstrSpec (xor_r64_r64_effect_step 0x10a2d8 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10a2db [0x48, 0x21, 0xDA] (fun s => s.RIP = 0x10a2db) (andR64R64Effect 0x10a2db 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a2db 2 3).toInstrSpec (and_r64_r64_effect_step 0x10a2db 0x48 0xda (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x10a2de [0x48, 0x31, 0xD0] (fun s => s.RIP = 0x10a2de) (xorR64R64Effect 0x10a2de 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2de 0 2).toInstrSpec (xor_r64_r64_effect_step 0x10a2de 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x10a2e1 [0x48, 0x01, 0xD2] (fun s => s.RIP = 0x10a2e1) (addR64R64Effect 0x10a2e1 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a2e1 2 2).toInstrSpec (add_r64_r64_effect_step 0x10a2e1 0x48 0xd2 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10a2e4 [0x4C, 0x31, 0xDA] (fun s => s.RIP = 0x10a2e4) (xorR64R64Effect 0x10a2e4 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2e4 2 11).toInstrSpec (xor_r64_r64_effect_step 0x10a2e4 0x4c 0xda (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10a2e7 [0x49, 0x89, 0xCF] (fun s => s.RIP = 0x10a2e7) (movR64R64Effect 0x10a2e7 15 1)
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10a2e7 15 1).toInstrSpec (mov_r64_r64_effect_step 0x10a2e7 0x49 0xcf (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x10a2ea [0x49, 0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x10a2ea) (shrR64Effect 0x10a2ea 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a2ea 4 15 2).toInstrSpec (shr_r64_imm8_effect_step 0x10a2ea 0x49 0xef 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10a2ee [0x49, 0x31, 0xF7] (fun s => s.RIP = 0x10a2ee) (xorR64R64Effect 0x10a2ee 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2ee 15 6).toInstrSpec (xor_r64_r64_effect_step 0x10a2ee 0x49 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 91), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2b7) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 95), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2ba) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 97), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2bd) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 97), (7, 7), (8, 63), (9, 99), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2c0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 97), (7, 7), (8, 63), (9, 101), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2c3) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 97), (7, 7), (8, 63), (9, 103), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2c6) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 97), (7, 7), (8, 63), (9, 105), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2c9) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 105), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2cc) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 109), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2cf) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2d2) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 67), (1, 83), (2, 113), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2d5) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 67), (1, 83), (2, 115), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2d8) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 67), (1, 83), (2, 117), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2db) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 67), (1, 83), (2, 119), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2de) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 121), (1, 83), (2, 119), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2e1) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 121), (1, 83), (2, 123), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2e4) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2e7) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2ea) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f38 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2ee) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f39 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 121), (1, 83), (2, 125), (3, 75), (4, 4), (6, 97), (7, 7), (8, 107), (9, 111), (10, 79), (11, 65), (14, 93), (15, 131), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2f1) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_2 code

theorem rest_l10a26a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a26a bytes_l10a26a) (entryMap (live .l10a26a))
      259 0x10a26a bytes_l10a26a b_l10a26a := by
  have f0 : InstrSpec 0x10a26a [0x4C, 0x8B, 0x0E] (LoadPre 0x10a26a (fun s => AddrMode.addr (.base 6 .none) s (0x10a26a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a26a 9 (.base 6 .none))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10a26a 9 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10a26a 0x4c (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10a26d [0x4C, 0x8B, 0x56, 0x08] (LoadPre 0x10a26d (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a26d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a26d 10 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10a26d 10 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10a26d 0x4c (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10a271 [0x4C, 0x8B, 0x7E, 0x10] (LoadPre 0x10a271 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a271 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a271 15 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10a271 15 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a271 0x4c (by decide) 7 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10a275 [0x4C, 0x8B, 0x76, 0x18] (LoadPre 0x10a275 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a275 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a275 14 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10a275 14 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a275 0x4c (by decide) 6 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10a279 [0x48, 0x8B, 0x56, 0x20] (LoadPre 0x10a279 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x10a279 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a279 2 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10a279 2 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10a279 0x48 (by decide) 2 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10a27d [0x4C, 0x8B, 0x46, 0x28] (LoadPre 0x10a27d (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x10a27d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a27d 8 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10a27d 8 (.base 6 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10a27d 0x4c (by decide) 0 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10a281 [0x4C, 0x8B, 0x5E, 0x30] (LoadPre 0x10a281 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x10a281 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a281 11 (.base 6 (.d8 0x30)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x10a281 11 (.base 6 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10a281 0x4c (by decide) 3 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10a285 [0x48, 0x8B, 0x46, 0x38] (LoadPre 0x10a285 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x10a285 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a285 0 (.base 6 (.d8 0x38)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10a285 0 (.base 6 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10a285 0x48 (by decide) 0 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10a289 [0x4C, 0x89, 0xC9] (fun s => s.RIP = 0x10a289) (movR64R64Effect 0x10a289 1 9)
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a289 1 9).toInstrSpec (mov_r64_r64_effect_step 0x10a289 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10a28c [0x48, 0xD1, 0xE9] (fun s => s.RIP = 0x10a28c) (shrR64Effect 0x10a28c 3 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a28c 3 1 1).toInstrSpec (shr_r64_one_effect_step 0x10a28c 0x48 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10a28f [0x4C, 0x31, 0xD1] (fun s => s.RIP = 0x10a28f) (xorR64R64Effect 0x10a28f 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a28f 1 10).toInstrSpec (xor_r64_r64_effect_step 0x10a28f 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10a292 [0x48, 0xBB, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55] (fun s => s.RIP = 0x10a292) (movR64Imm64Effect 0x10a292 3 0x5555555555555555)
      [] [] [.reg 3, .rip] :=
    (movR64Imm64Effect_footprint 0x10a292 3 0x5555555555555555).toInstrSpec (mov_r64_imm64_effect_step 0x10a292 0x48 0xbb (by decide) (by decide) 0x5555555555555555) pre_rip
  have f12 : InstrSpec 0x10a29c [0x48, 0x21, 0xD9] (fun s => s.RIP = 0x10a29c) (andR64R64Effect 0x10a29c 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a29c 1 3).toInstrSpec (and_r64_r64_effect_step 0x10a29c 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10a29f [0x49, 0x31, 0xCA] (fun s => s.RIP = 0x10a29f) (xorR64R64Effect 0x10a29f 10 1)
      [.gpr 10, .gpr 1] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a29f 10 1).toInstrSpec (xor_r64_r64_effect_step 0x10a29f 0x49 0xca (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10a2a2 [0x48, 0x01, 0xC9] (fun s => s.RIP = 0x10a2a2) (addR64R64Effect 0x10a2a2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10a2a2 1 1).toInstrSpec (add_r64_r64_effect_step 0x10a2a2 0x48 0xc9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10a2a5 [0x4C, 0x31, 0xC9] (fun s => s.RIP = 0x10a2a5) (xorR64R64Effect 0x10a2a5 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2a5 1 9).toInstrSpec (xor_r64_r64_effect_step 0x10a2a5 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10a2a8 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10a2a8) (movR64R64Effect 0x10a2a8 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10a2a8 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10a2a8 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10a2ab [0x48, 0xD1, 0xEE] (fun s => s.RIP = 0x10a2ab) (shrR64Effect 0x10a2ab 3 6 1)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x10a2ab 3 6 1).toInstrSpec (shr_r64_one_effect_step 0x10a2ab 0x48 0xee (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10a2ae [0x4C, 0x31, 0xF6] (fun s => s.RIP = 0x10a2ae) (xorR64R64Effect 0x10a2ae 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10a2ae 6 14).toInstrSpec (xor_r64_r64_effect_step 0x10a2ae 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10a2b1 [0x48, 0x21, 0xDE] (fun s => s.RIP = 0x10a2b1) (andR64R64Effect 0x10a2b1 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10a2b1 6 3).toInstrSpec (and_r64_r64_effect_step 0x10a2b1 0x48 0xde (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (6, 6), (7, 7), (9, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a26d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (6, 6), (7, 7), (9, 53), (10, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a271) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 4), (6, 6), (7, 7), (9, 53), (10, 55), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a275) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 4), (6, 6), (7, 7), (9, 53), (10, 55), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a279) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 61), (4, 4), (6, 6), (7, 7), (9, 53), (10, 55), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a27d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 61), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 55), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a281) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 61), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 55), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a285) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 61), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 55), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a289) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 69), (2, 61), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 55), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a28c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 71), (2, 61), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 55), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a28f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (1, 73), (2, 61), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 55), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a292) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 67), (1, 73), (2, 61), (3, 75), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 55), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a29c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 67), (1, 77), (2, 61), (3, 75), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 55), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a29f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 67), (1, 77), (2, 61), (3, 75), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2a2) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 67), (1, 81), (2, 61), (3, 75), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2a5) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 6), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2a8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 85), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2ab) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 87), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2ae) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 89), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2b1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 67), (1, 83), (2, 61), (3, 75), (4, 4), (6, 91), (7, 7), (8, 63), (9, 53), (10, 79), (11, 65), (14, 59), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a2b4) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a26a_1 code

theorem block_l10a26a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a26a :=
  Rest.liftedBlock (rest_l10a26a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a26a x hx)

theorem rest_l10a5d7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a5d7 bytes_l10a5d7) (entryMap (live .l10a5d7))
      4 0x10a5d7 bytes_l10a5d7 b_l10a5d7 := by
  have f0 : InstrSpec 0x10a5d7 [0x31, 0xFF] (fun s => s.RIP = 0x10a5d7) (xorR32R32Effect 0x10a5d7 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a5d7 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x10a5d7 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x10a5d9 [0x31, 0xF6] (fun s => s.RIP = 0x10a5d9) (xorR32R32Effect 0x10a5d9 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a5d9 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10a5d9 0xf6 (by decide)) pre_rip
  have f2 : InstrSpec 0x10a5db [0x48, 0xC7, 0xC2, 0x30, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10a5db) (movR64Imm32Effect 0x10a5db 2 0x201130)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a5db 2 0x201130).toInstrSpec (mov_r64_imm32_effect_step 0x10a5db 0x48 0xc2 (by decide) (by decide) (by decide) 0x201130) pre_rip
  have f3 : InstrSpec 0x10a5e2 [0xE8, 0x50, 0x92, 0xFF, 0xFF] (PushPre 0x10a5e2 5) (callEffect (fun _ => 0x103837) 0x10a5e7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a5e2 0x103837 0x10a5e7).toInstrSpec (call_rel32_effect_step 0x10a5e2 0xffff9250 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x10a5d9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a5db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a5e2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10a5d7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a5d7 :=
  Rest.liftedBlock (rest_l10a5d7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a5d7 x hx)

theorem rest_l10a5e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a5e7 bytes_l10a5e7) (entryMap (live .l10a5e7))
      4 0x10a5e7 bytes_l10a5e7 b_l10a5e7 := by
  have f0 : InstrSpec 0x10a5e7 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a5e7) (movR32Imm32Effect 0x10a5e7 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10a5e7 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10a5e7 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x10a5ec [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a5ec) (movR32Imm32Effect 0x10a5ec 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a5ec 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10a5ec 0xbe (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x10a5f1 [0x48, 0xC7, 0xC2, 0x48, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10a5f1) (movR64Imm32Effect 0x10a5f1 2 0x201148)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a5f1 2 0x201148).toInstrSpec (mov_r64_imm32_effect_step 0x10a5f1 0x48 0xc2 (by decide) (by decide) (by decide) 0x201148) pre_rip
  have f3 : InstrSpec 0x10a5f8 [0xE8, 0x3A, 0x92, 0xFF, 0xFF] (PushPre 0x10a5f8 5) (callEffect (fun _ => 0x103837) 0x10a5fd)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a5f8 0x103837 0x10a5fd).toInstrSpec (call_rel32_effect_step 0x10a5f8 0xffff923a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10a5ec) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a5f1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a5f8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10a5e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a5e7 :=
  Rest.liftedBlock (rest_l10a5e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a5e7 x hx)

theorem rest_l10a5fd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a5fd bytes_l10a5fd) (entryMap (live .l10a5fd))
      4 0x10a5fd bytes_l10a5fd b_l10a5fd := by
  have f0 : InstrSpec 0x10a5fd [0xBF, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a5fd) (movR32Imm32Effect 0x10a5fd 5 7 0x2)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10a5fd 5 7 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x10a5fd 0xbf (by decide) 0x2) pre_rip
  have f1 : InstrSpec 0x10a602 [0xBE, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a602) (movR32Imm32Effect 0x10a602 5 6 0x2)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a602 5 6 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x10a602 0xbe (by decide) 0x2) pre_rip
  have f2 : InstrSpec 0x10a607 [0x48, 0xC7, 0xC2, 0x60, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10a607) (movR64Imm32Effect 0x10a607 2 0x201160)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a607 2 0x201160).toInstrSpec (mov_r64_imm32_effect_step 0x10a607 0x48 0xc2 (by decide) (by decide) (by decide) 0x201160) pre_rip
  have f3 : InstrSpec 0x10a60e [0xE8, 0x24, 0x92, 0xFF, 0xFF] (PushPre 0x10a60e 5) (callEffect (fun _ => 0x103837) 0x10a613)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a60e 0x103837 0x10a613).toInstrSpec (call_rel32_effect_step 0x10a60e 0xffff9224 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10a602) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a607) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a60e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10a5fd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a5fd :=
  Rest.liftedBlock (rest_l10a5fd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a5fd x hx)

theorem rest_l10a613 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a613 bytes_l10a613) (entryMap (live .l10a613))
      4 0x10a613 bytes_l10a613 b_l10a613 := by
  have f0 : InstrSpec 0x10a613 [0xBF, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a613) (movR32Imm32Effect 0x10a613 5 7 0x3)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10a613 5 7 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x10a613 0xbf (by decide) 0x3) pre_rip
  have f1 : InstrSpec 0x10a618 [0xBE, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a618) (movR32Imm32Effect 0x10a618 5 6 0x3)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a618 5 6 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x10a618 0xbe (by decide) 0x3) pre_rip
  have f2 : InstrSpec 0x10a61d [0x48, 0xC7, 0xC2, 0x78, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10a61d) (movR64Imm32Effect 0x10a61d 2 0x201178)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a61d 2 0x201178).toInstrSpec (mov_r64_imm32_effect_step 0x10a61d 0x48 0xc2 (by decide) (by decide) (by decide) 0x201178) pre_rip
  have f3 : InstrSpec 0x10a624 [0xE8, 0x0E, 0x92, 0xFF, 0xFF] (PushPre 0x10a624 5) (callEffect (fun _ => 0x103837) 0x10a629)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a624 0x103837 0x10a629).toInstrSpec (call_rel32_effect_step 0x10a624 0xffff920e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10a618) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a61d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a624) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10a613 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a613 :=
  Rest.liftedBlock (rest_l10a613 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a613 x hx)

theorem rest_l10a629 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a629 bytes_l10a629) (entryMap (live .l10a629))
      4 0x10a629 bytes_l10a629 b_l10a629 := by
  have f0 : InstrSpec 0x10a629 [0xBF, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a629) (movR32Imm32Effect 0x10a629 5 7 0x4)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10a629 5 7 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10a629 0xbf (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x10a62e [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a62e) (movR32Imm32Effect 0x10a62e 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a62e 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10a62e 0xbe (by decide) 0x4) pre_rip
  have f2 : InstrSpec 0x10a633 [0x48, 0xC7, 0xC2, 0x90, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10a633) (movR64Imm32Effect 0x10a633 2 0x201190)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a633 2 0x201190).toInstrSpec (mov_r64_imm32_effect_step 0x10a633 0x48 0xc2 (by decide) (by decide) (by decide) 0x201190) pre_rip
  have f3 : InstrSpec 0x10a63a [0xE8, 0xF8, 0x91, 0xFF, 0xFF] (PushPre 0x10a63a 5) (callEffect (fun _ => 0x103837) 0x10a63f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a63a 0x103837 0x10a63f).toInstrSpec (call_rel32_effect_step 0x10a63a 0xffff91f8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10a62e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a633) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a63a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10a629 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a629 :=
  Rest.liftedBlock (rest_l10a629 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a629 x hx)

theorem rest_l10a63f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a63f bytes_l10a63f) (entryMap (live .l10a63f))
      4 0x10a63f bytes_l10a63f b_l10a63f := by
  have f0 : InstrSpec 0x10a63f [0xBF, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a63f) (movR32Imm32Effect 0x10a63f 5 7 0x5)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10a63f 5 7 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x10a63f 0xbf (by decide) 0x5) pre_rip
  have f1 : InstrSpec 0x10a644 [0xBE, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a644) (movR32Imm32Effect 0x10a644 5 6 0x5)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a644 5 6 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x10a644 0xbe (by decide) 0x5) pre_rip
  have f2 : InstrSpec 0x10a649 [0x48, 0xC7, 0xC2, 0xA8, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10a649) (movR64Imm32Effect 0x10a649 2 0x2011a8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a649 2 0x2011a8).toInstrSpec (mov_r64_imm32_effect_step 0x10a649 0x48 0xc2 (by decide) (by decide) (by decide) 0x2011a8) pre_rip
  have f3 : InstrSpec 0x10a650 [0xE8, 0xE2, 0x91, 0xFF, 0xFF] (PushPre 0x10a650 5) (callEffect (fun _ => 0x103837) 0x10a655)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a650 0x103837 0x10a655).toInstrSpec (call_rel32_effect_step 0x10a650 0xffff91e2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10a644) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a649) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a650) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10a63f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a63f :=
  Rest.liftedBlock (rest_l10a63f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a63f x hx)

theorem rest_l10a655 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a655 bytes_l10a655) (entryMap (live .l10a655))
      4 0x10a655 bytes_l10a655 b_l10a655 := by
  have f0 : InstrSpec 0x10a655 [0xBF, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a655) (movR32Imm32Effect 0x10a655 5 7 0x6)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10a655 5 7 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x10a655 0xbf (by decide) 0x6) pre_rip
  have f1 : InstrSpec 0x10a65a [0xBE, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a65a) (movR32Imm32Effect 0x10a65a 5 6 0x6)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a65a 5 6 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x10a65a 0xbe (by decide) 0x6) pre_rip
  have f2 : InstrSpec 0x10a65f [0x48, 0xC7, 0xC2, 0xC0, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10a65f) (movR64Imm32Effect 0x10a65f 2 0x2011c0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a65f 2 0x2011c0).toInstrSpec (mov_r64_imm32_effect_step 0x10a65f 0x48 0xc2 (by decide) (by decide) (by decide) 0x2011c0) pre_rip
  have f3 : InstrSpec 0x10a666 [0xE8, 0xCC, 0x91, 0xFF, 0xFF] (PushPre 0x10a666 5) (callEffect (fun _ => 0x103837) 0x10a66b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a666 0x103837 0x10a66b).toInstrSpec (call_rel32_effect_step 0x10a666 0xffff91cc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10a65a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a65f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a666) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10a655 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a655 :=
  Rest.liftedBlock (rest_l10a655 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a655 x hx)

theorem rest_l10a66b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a66b bytes_l10a66b) (entryMap (live .l10a66b))
      4 0x10a66b bytes_l10a66b b_l10a66b := by
  have f0 : InstrSpec 0x10a66b [0xBF, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a66b) (movR32Imm32Effect 0x10a66b 5 7 0x7)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10a66b 5 7 0x7).toInstrSpec (mov_r32_imm32_effect_step 0x10a66b 0xbf (by decide) 0x7) pre_rip
  have f1 : InstrSpec 0x10a670 [0xBE, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a670) (movR32Imm32Effect 0x10a670 5 6 0x7)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a670 5 6 0x7).toInstrSpec (mov_r32_imm32_effect_step 0x10a670 0xbe (by decide) 0x7) pre_rip
  have f2 : InstrSpec 0x10a675 [0x48, 0xC7, 0xC2, 0xD8, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10a675) (movR64Imm32Effect 0x10a675 2 0x2011d8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10a675 2 0x2011d8).toInstrSpec (mov_r64_imm32_effect_step 0x10a675 0x48 0xc2 (by decide) (by decide) (by decide) 0x2011d8) pre_rip
  have f3 : InstrSpec 0x10a67c [0xE8, 0xB6, 0x91, 0xFF, 0xFF] (PushPre 0x10a67c 5) (callEffect (fun _ => 0x103837) 0x10a681)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a67c 0x103837 0x10a681).toInstrSpec (call_rel32_effect_step 0x10a67c 0xffff91b6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10a670) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a675) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10a67c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x103837) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10a66b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a66b :=
  Rest.liftedBlock (rest_l10a66b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a66b x hx)

theorem rest_l10a681 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a681 bytes_l10a681) (entryMap (live .l10a681))
      2 0x10a681 bytes_l10a681 b_l10a681 := by
  have f0 : InstrSpec 0x10a681 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a681) (fun _ => nopEffect 0x10a681 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10a681 10).toInstrSpec (nop_m_effect_step 0x10a681 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10a68b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x10a68b) (fun _ => nopEffect 0x10a68b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10a68b 5).toInstrSpec (nop_m_effect_step 0x10a68b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a68b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a690) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l10a681 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a681 :=
  Rest.liftedBlock (rest_l10a681 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a681 x hx)

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

theorem_by block_l10a210_eval :
    program.runBlock (dialect code) ⟨.l10a210, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a224_eval :
    program.runBlock (dialect code) ⟨.l10a224, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a22e_eval :
    program.runBlock (dialect code) ⟨.l10a22e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a238_eval :
    program.runBlock (dialect code) ⟨.l10a238, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a242_eval :
    program.runBlock (dialect code) ⟨.l10a242, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a24c_eval :
    program.runBlock (dialect code) ⟨.l10a24c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a256_eval :
    program.runBlock (dialect code) ⟨.l10a256, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a260_eval :
    program.runBlock (dialect code) ⟨.l10a260, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a5d7_eval :
    program.runBlock (dialect code) ⟨.l10a5d7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a5e7_eval :
    program.runBlock (dialect code) ⟨.l10a5e7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a5fd_eval :
    program.runBlock (dialect code) ⟨.l10a5fd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a613_eval :
    program.runBlock (dialect code) ⟨.l10a613, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a629_eval :
    program.runBlock (dialect code) ⟨.l10a629, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a63f_eval :
    program.runBlock (dialect code) ⟨.l10a63f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a655_eval :
    program.runBlock (dialect code) ⟨.l10a655, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a66b_eval :
    program.runBlock (dialect code) ⟨.l10a66b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a681_eval :
    program.runBlock (dialect code) ⟨.l10a681, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
