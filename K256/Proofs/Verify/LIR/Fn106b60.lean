import K256.Proofs.Verify.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l106b60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106b60 bytes_l106b60) (entryMap (live .l106b60))
      13 0x106b60 bytes_l106b60 b_l106b60 := by
  have f0 : InstrSpec 0x106b60 [0x55] (PushPre 0x106b60 1) (pushR64Effect 0x106b60 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106b60 1 5).toInstrSpec (push_r64_effect_step 0x106b60 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x106b61 [0x41, 0x57] (PushPre 0x106b61 2) (pushR64Effect 0x106b61 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106b61 2 15).toInstrSpec (push_r64_rex_effect_step 0x106b61 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x106b63 [0x41, 0x56] (PushPre 0x106b63 2) (pushR64Effect 0x106b63 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106b63 2 14).toInstrSpec (push_r64_rex_effect_step 0x106b63 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106b65 [0x41, 0x55] (PushPre 0x106b65 2) (pushR64Effect 0x106b65 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106b65 2 13).toInstrSpec (push_r64_rex_effect_step 0x106b65 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x106b67 [0x41, 0x54] (PushPre 0x106b67 2) (pushR64Effect 0x106b67 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106b67 2 12).toInstrSpec (push_r64_rex_effect_step 0x106b67 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x106b69 [0x53] (PushPre 0x106b69 1) (pushR64Effect 0x106b69 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106b69 1 3).toInstrSpec (push_r64_effect_step 0x106b69 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x106b6a [0x48, 0x83, 0xEC, 0x78] (fun s => s.RIP = 0x106b6a) (subR64Imm8Effect 0x106b6a 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x106b6a 4 0x78).toInstrSpec (sub_r64_imm8_effect_step 0x106b6a 0x48 0xec 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x106b6e [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x106b6e) (movR64R64Effect 0x106b6e 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x106b6e 3 7).toInstrSpec (mov_r64_r64_effect_step 0x106b6e 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x106b71 [0x89, 0xF5] (fun s => s.RIP = 0x106b71) (movR32R32Effect 0x106b71 2 5 6)
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x106b71 2 5 6).toInstrSpec (mov_r32_r32_effect_step 0x106b71 0xf5 (by decide)) pre_rip
  have f9 : InstrSpec 0x106b73 [0x40, 0x80, 0xE5, 0x20] (fun s => s.RIP = 0x106b73) (andR8Imm8Effect 0x106b73 4 5 0x20)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x106b73 4 5 0x20).toInstrSpec (and_r8_imm8_rex_effect_step 0x106b73 0x40 0xe5 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x106b77 [0x40, 0x80, 0xE6, 0x1F] (fun s => s.RIP = 0x106b77) (andR8Imm8Effect 0x106b77 4 6 0x1f)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x106b77 4 6 0x1f).toInstrSpec (and_r8_imm8_rex_effect_step 0x106b77 0x40 0xe6 0x1f (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x106b7b [0x40, 0x80, 0xFE, 0x1F] (fun s => s.RIP = 0x106b7b) (cmpR8Imm8Effect 0x106b7b 4 6 0x1f)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x106b7b 4 6 0x1f).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x106b7b 0x40 0xfe 0x1f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b61) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b63) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b65) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b67) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b69) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b6a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b6e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b71) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b73) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b77) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b7b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 71), (6, 73), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b7f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel8_effect_step 0x106b7f 5 0x5d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106b60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106b60 :=
  Rest.liftedBlock (rest_l106b60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106b60 x hx)

theorem rest_l106b81 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106b81 bytes_l106b81) (entryMap (live .l106b81))
      5 0x106b81 bytes_l106b81 b_l106b81 := by
  have f0 : InstrSpec 0x106b81 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x106b81) (movR64R64Effect 0x106b81 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x106b81 14 2).toInstrSpec (mov_r64_r64_effect_step 0x106b81 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106b84 [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x106b84) (leaR64Effect 0x106b84 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106b84 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x106b84 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106b89 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x106b89) (movR64R64Effect 0x106b89 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x106b89 6 2).toInstrSpec (mov_r64_r64_effect_step 0x106b89 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106b8c [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106b8c) (movR32Imm32Effect 0x106b8c 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x106b8c 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x106b8c 0xba (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x106b91 [0xE8, 0xEA, 0x0F, 0x02, 0x00] (PushPre 0x106b91 5) (callEffect (fun _ => 0x127b80) 0x106b96)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106b91 0x127b80 0x106b96).toInstrSpec (call_rel32_effect_step 0x106b91 0x20fea (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b84) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b89) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b8c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b91) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l106b81 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106b81 :=
  Rest.liftedBlock (rest_l106b81 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106b81 x hx)

theorem rest_l106b96 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106b96 bytes_l106b96) (entryMap (live .l106b96))
      3 0x106b96 bytes_l106b96 b_l106b96 := by
  have f0 : InstrSpec 0x106b96 [0x8B, 0x44, 0x24, 0x40] (LoadPre 0x106b96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106b96 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106b96 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106b96 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r32_m32_low_effect_step 0x106b96 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106b9a [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x106b9a) (cmpR32Imm8Effect 0x106b9a 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106b9a 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106b9a 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b9a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b9d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x106b9d 5 0xb1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106b96 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106b96 :=
  Rest.liftedBlock (rest_l106b96 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106b96 x hx)

theorem rest_l106ba3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106ba3 bytes_l106ba3) (entryMap (live .l106ba3))
      3 0x106ba3 bytes_l106ba3 b_l106ba3 := by
  have f0 : InstrSpec 0x106ba3 [0x48, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x106ba3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x106ba3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106ba3 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106ba3 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x106ba3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106ba8 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x106ba8) (cmpR64Imm8Effect 0x106ba8 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x106ba8 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x106ba8 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ba8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bac) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x106bac 5 0x1ff) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106ba3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106ba3 :=
  Rest.liftedBlock (rest_l106ba3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106ba3 x hx)

theorem rest_l106bb2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106bb2 bytes_l106bb2) (entryMap (live .l106bb2))
      6 0x106bb2 bytes_l106bb2 b_l106bb2 := by
  have f0 : InstrSpec 0x106bb2 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x106bb2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106bb2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106bb2 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x106bb2 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x106bb2 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106bb7 [0x44, 0x0F, 0xB6, 0x38] (LoadPre 0x106bb7 (fun s => AddrMode.addr (.base 0 .none) s (0x106bb7 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x106bb7 4 15 (.base 0 .none))
      [.gpr 0] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x106bb7 4 15 (.base 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x106bb7 0x44 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106bbb [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x106bbb) (movR32R32Effect 0x106bbb 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106bbb 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x106bbb 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106bbe [0x41, 0x83, 0xE7, 0x7F] (fun s => s.RIP = 0x106bbe) (andR32Imm8Effect 0x106bbe 4 15 0x7f)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x106bbe 4 15 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x106bbe 0x41 0xe7 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106bc2 [0x84, 0xC0] (fun s => s.RIP = 0x106bc2) (testR8R8Effect 0x106bc2 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x106bc2 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x106bc2 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bb7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bbb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bbe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bc2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 59), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bc4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x106bc4 8 0x32) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106bb2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106bb2 :=
  Rest.liftedBlock (rest_l106bb2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106bb2 x hx)

theorem rest_l106bc6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106bc6 bytes_l106bc6) (entryMap (live .l106bc6))
      2 0x106bc6 bytes_l106bc6 b_l106bc6 := by
  have f0 : InstrSpec 0x106bc6 [0x41, 0x80, 0xFF, 0x1F] (fun s => s.RIP = 0x106bc6) (cmpR8Imm8Effect 0x106bc6 4 15 0x1f)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x106bc6 4 15 0x1f).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x106bc6 0x41 0xff 0x1f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x106bca 2 0x185) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106bc6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106bc6 :=
  Rest.liftedBlock (rest_l106bc6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106bc6 x hx)

theorem rest_l106bd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106bd0 bytes_l106bd0) (entryMap (live .l106bd0))
      4 0x106bd0 bytes_l106bd0 b_l106bd0 := by
  have f0 : InstrSpec 0x106bd0 [0x40, 0xC0, 0xED, 0x05] (fun s => s.RIP = 0x106bd0) (shrR8Effect 0x106bd0 4 5 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR8Effect_footprint 0x106bd0 4 5 5).toInstrSpec (shr_r8_imm8_rex_effect_step 0x106bd0 0x40 0xed 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106bd4 [0x40, 0x88, 0x6B, 0x04] (StorePre 0x106bd4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106bd4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106bd4 4 5 (.base 3 (.d8 0x4)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106bd4 4 5 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x106bd4 0x40 (by decide) 5 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x106bd8 [0x44, 0x89, 0x7B, 0x08] (StorePre 0x106bd8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106bd8 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x106bd8 15 (.base 3 (.d8 0x8)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x106bd8 15 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_effect_step 0x106bd8 0x44 (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bd4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bd8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bdc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x106bdc 0xf (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106bd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106bd0 :=
  Rest.liftedBlock (rest_l106bd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106bd0 x hx)

theorem rest_l106bde [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106bde bytes_l106bde) (entryMap (live .l106bde))
      4 0x106bde bytes_l106bde b_l106bde := by
  have f0 : InstrSpec 0x106bde [0x40, 0x0F, 0xB6, 0xC6] (fun s => s.RIP = 0x106bde) (movzxR32R8Effect 0x106bde 4 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x106bde 4 0 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x106bde 0x40 (by decide) 0xc6 (by decide)) pre_rip
  have f1 : InstrSpec 0x106be2 [0x40, 0xC0, 0xED, 0x05] (fun s => s.RIP = 0x106be2) (shrR8Effect 0x106be2 4 5 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR8Effect_footprint 0x106be2 4 5 5).toInstrSpec (shr_r8_imm8_rex_effect_step 0x106be2 0x40 0xed 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106be6 [0x40, 0x88, 0x6B, 0x04] (StorePre 0x106be6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106be6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106be6 4 5 (.base 3 (.d8 0x4)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106be6 4 5 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x106be6 0x40 (by decide) 5 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x106bea [0x89, 0x43, 0x08] (StorePre 0x106bea 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106bea + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106bea 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106bea 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x106bea 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106be2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106be6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bea) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bed) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l106bde [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106bde :=
  Rest.liftedBlock (rest_l106bde code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106bde x hx)

theorem rest_l106bed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106bed bytes_l106bed) (entryMap (live .l106bed))
      2 0x106bed bytes_l106bed b_l106bed := by
  have f0 : InstrSpec 0x106bed [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x106bed 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106bed + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106bed 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x106bed 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x106bed (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bf3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel32_effect_step 0x106bf3 0x173 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106bed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106bed :=
  Rest.liftedBlock (rest_l106bed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106bed x hx)

theorem rest_l106bf8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106bf8 bytes_l106bf8) (entryMap (live .l106bf8))
      2 0x106bf8 bytes_l106bf8 b_l106bf8 := by
  have f0 : InstrSpec 0x106bf8 [0x45, 0x84, 0xFF] (fun s => s.RIP = 0x106bf8) (testR8R8Effect 0x106bf8 3 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x106bf8 3 15 15).toInstrSpec (test_r8_r8_rex_effect_step 0x106bf8 0x45 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bfb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x106bfb 4 0x154) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106bf8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106bf8 :=
  Rest.liftedBlock (rest_l106bf8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106bf8 x hx)

theorem rest_l106c01 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106c01 bytes_l106c01) (entryMap (live .l106c01))
      4 0x106c01 bytes_l106c01 b_l106c01 := by
  have f0 : InstrSpec 0x106c01 [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x106c01) (leaR64Effect 0x106c01 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106c01 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x106c01 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106c06 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x106c06) (movR64R64Effect 0x106c06 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x106c06 6 14).toInstrSpec (mov_r64_r64_effect_step 0x106c06 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106c09 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106c09) (movR32Imm32Effect 0x106c09 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x106c09 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x106c09 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x106c0e [0xE8, 0x6D, 0x0F, 0x02, 0x00] (PushPre 0x106c0e 5) (callEffect (fun _ => 0x127b80) 0x106c13)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106c0e 0x127b80 0x106c13).toInstrSpec (call_rel32_effect_step 0x106c0e 0x20f6d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c06) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c09) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c0e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l106c01 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106c01 :=
  Rest.liftedBlock (rest_l106c01 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106c01 x hx)

theorem rest_l106c13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106c13 bytes_l106c13) (entryMap (live .l106c13))
      3 0x106c13 bytes_l106c13 b_l106c13 := by
  have f0 : InstrSpec 0x106c13 [0x8B, 0x44, 0x24, 0x40] (LoadPre 0x106c13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106c13 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c13 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106c13 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r32_m32_low_effect_step 0x106c13 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106c17 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x106c17) (cmpR32Imm8Effect 0x106c17 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106c17 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106c17 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c17) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c1a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x106c1a 5 0x38) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106c13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106c13 :=
  Rest.liftedBlock (rest_l106c13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106c13 x hx)

theorem rest_l106c1c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106c1c bytes_l106c1c) (entryMap (live .l106c1c))
      3 0x106c1c bytes_l106c1c b_l106c1c := by
  have f0 : InstrSpec 0x106c1c [0x48, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x106c1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x106c1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c1c 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106c1c 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x106c1c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106c21 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x106c21) (cmpR64Imm8Effect 0x106c21 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x106c21 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x106c21 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c21) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c25) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x106c25 5 0x186) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106c1c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106c1c :=
  Rest.liftedBlock (rest_l106c1c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106c1c x hx)

theorem rest_l106c2b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106c2b bytes_l106c2b) (entryMap (live .l106c2b))
      9 0x106c2b bytes_l106c2b b_l106c2b := by
  have f0 : InstrSpec 0x106c2b [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x106c2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106c2b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c2b 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x106c2b 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x106c2b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106c30 [0x44, 0x0F, 0xB6, 0x20] (LoadPre 0x106c30 (fun s => AddrMode.addr (.base 0 .none) s (0x106c30 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x106c30 4 12 (.base 0 .none))
      [.gpr 0] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x106c30 4 12 (.base 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x106c30 0x44 (by decide) 4 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106c34 [0x44, 0x89, 0xE0] (fun s => s.RIP = 0x106c34) (movR32R32Effect 0x106c34 3 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106c34 3 0 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x106c34 0x44 0xe0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106c37 [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x106c37) (movR32R32Effect 0x106c37 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106c37 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x106c37 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106c3a [0xC1, 0xE1, 0x07] (fun s => s.RIP = 0x106c3a) (shlR32Effect 0x106c3a 3 1 7)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106c3a 3 1 7).toInstrSpec (shl_r32_imm8_effect_step 0x106c3a 0xe1 0x7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x106c3d [0x41, 0x83, 0xE4, 0x7F] (fun s => s.RIP = 0x106c3d) (andR32Imm8Effect 0x106c3d 4 12 0x7f)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x106c3d 4 12 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x106c3d 0x41 0xe4 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x106c41 [0x41, 0x09, 0xCC] (fun s => s.RIP = 0x106c41) (orR32R32Effect 0x106c41 3 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106c41 3 12 1).toInstrSpec (or_r32_r32_rex_effect_step 0x106c41 0x41 0xcc (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x106c44 [0x84, 0xC0] (fun s => s.RIP = 0x106c44) (testR8R8Effect 0x106c44 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x106c44 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x106c44 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c30) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c34) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c37) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c3a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c3d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c41) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c44) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c46) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel32_effect_step 0x106c46 8 0x93) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106c2b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106c2b :=
  Rest.liftedBlock (rest_l106c2b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106c2b x hx)

theorem rest_l106c4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106c4c bytes_l106c4c) (entryMap (live .l106c4c))
      2 0x106c4c bytes_l106c4c b_l106c4c := by
  have f0 : InstrSpec 0x106c4c [0x45, 0x89, 0xE7] (fun s => s.RIP = 0x106c4c) (movR32R32Effect 0x106c4c 3 15 12)
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x106c4c 3 15 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x106c4c 0x45 0xe7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c4f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x106c4f 0xffffff7c (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106c4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106c4c :=
  Rest.liftedBlock (rest_l106c4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106c4c x hx)

theorem rest_l106c54 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106c54 bytes_l106c54) (entryMap (live .l106c54))
      14 0x106c54 bytes_l106c54 b_l106c54 := by
  have f0 : InstrSpec 0x106c54 [0x8B, 0x4C, 0x24, 0x44] (LoadPre 0x106c54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x106c54 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c54 1 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x106c54 1 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x106c54 1 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106c58 [0x48, 0x8B, 0x54, 0x24, 0x48] (LoadPre 0x106c58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106c58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c58 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x106c58 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x106c58 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106c5d [0x48, 0x8B, 0x74, 0x24, 0x50] (LoadPre 0x106c5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x106c5d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c5d 6 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106c5d 6 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x106c5d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106c62 [0x48, 0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x106c62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x106c62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c62 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106c62 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x106c62 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x106c67 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x106c67 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106c67 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c67 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106c67 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x106c67 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x106c6c [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x106c6c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x106c6c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c6c 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106c6c 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x106c6c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x106c71 [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x106c71 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106c71 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c71 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106c71 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x106c71 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x106c76 [0x48, 0x8B, 0x7C, 0x24, 0x68] (LoadPre 0x106c76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x106c76 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c76 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106c76 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x106c76 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x106c7b [0x48, 0x89, 0x7C, 0x24, 0x30] (StorePre 0x106c7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106c7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c7b 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106c7b 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x106c7b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x106c80 [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x106c80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x106c80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c80 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106c80 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x106c80 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x106c85 [0x48, 0x89, 0x7C, 0x24, 0x38] (StorePre 0x106c85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x106c85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c85 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106c85 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x106c85 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x106c8a [0x89, 0x4C, 0x24, 0x0C] (StorePre 0x106c8a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106c8a + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x106c8a 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106c8a 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x106c8a 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x106c8e [0x48, 0x89, 0x54, 0x24, 0x10] (StorePre 0x106c8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106c8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c8e 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106c8e 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x106c8e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x106c93 [0x48, 0x89, 0x74, 0x24, 0x18] (StorePre 0x106c93 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x106c93 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106c93 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106c93 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x106c93 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c58) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c5d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c62) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c67) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c6c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c71) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c76) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c7b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c80) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c85) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c8a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c8e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c93) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c98) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l106c54 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106c54 :=
  Rest.liftedBlock (rest_l106c54 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106c54 x hx)

theorem rest_l106c98 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106c98 bytes_l106c98) (entryMap (live .l106c98))
      17 0x106c98 bytes_l106c98 b_l106c98 := by
  have f0 : InstrSpec 0x106c98 [0x8B, 0x54, 0x24, 0x3C] (LoadPre 0x106c98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x106c98 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c98 2 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x106c98 2 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x106c98 2 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106c9c [0x89, 0x53, 0x34] (StorePre 0x106c9c 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x106c9c + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106c9c 2 (.base 3 (.d8 0x34)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106c9c 2 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x106c9c 2 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x106c9f [0x48, 0x8B, 0x54, 0x24, 0x35] (LoadPre 0x106c9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x106c9f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106c9f 2 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x106c9f 2 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (mov_r64_m64_effect_step 0x106c9f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106ca4 [0x48, 0x89, 0x53, 0x2D] (StorePre 0x106ca4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x106ca4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106ca4 2 (.base 3 (.d8 0x2d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106ca4 2 (.base 3 (.d8 0x2d))).toInstrSpec (mov_m64_r64_effect_step 0x106ca4 0x48 (by decide) 2 (.base 3 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106ca8 [0x48, 0x8B, 0x54, 0x24, 0x2D] (LoadPre 0x106ca8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x106ca8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106ca8 2 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x106ca8 2 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (mov_r64_m64_effect_step 0x106ca8 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x106cad [0x48, 0x89, 0x53, 0x25] (StorePre 0x106cad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x106cad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106cad 2 (.base 3 (.d8 0x25)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106cad 2 (.base 3 (.d8 0x25))).toInstrSpec (mov_m64_r64_effect_step 0x106cad 0x48 (by decide) 2 (.base 3 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x106cb1 [0x48, 0x8B, 0x54, 0x24, 0x25] (LoadPre 0x106cb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x106cb1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106cb1 2 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x106cb1 2 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (mov_r64_m64_effect_step 0x106cb1 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x106cb6 [0x48, 0x89, 0x53, 0x1D] (StorePre 0x106cb6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x106cb6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106cb6 2 (.base 3 (.d8 0x1d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106cb6 2 (.base 3 (.d8 0x1d))).toInstrSpec (mov_m64_r64_effect_step 0x106cb6 0x48 (by decide) 2 (.base 3 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x106cba [0x48, 0x8B, 0x54, 0x24, 0x1D] (LoadPre 0x106cba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x106cba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106cba 2 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x106cba 2 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_r64_m64_effect_step 0x106cba 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x106cbf [0x48, 0x89, 0x53, 0x15] (StorePre 0x106cbf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x106cbf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106cbf 2 (.base 3 (.d8 0x15)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106cbf 2 (.base 3 (.d8 0x15))).toInstrSpec (mov_m64_r64_effect_step 0x106cbf 0x48 (by decide) 2 (.base 3 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x106cc3 [0x48, 0x8B, 0x54, 0x24, 0x0D] (LoadPre 0x106cc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106cc3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106cc3 2 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x106cc3 2 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_r64_m64_effect_step 0x106cc3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x106cc8 [0x48, 0x8B, 0x74, 0x24, 0x15] (LoadPre 0x106cc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x106cc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106cc8 6 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x106cc8 6 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_r64_m64_effect_step 0x106cc8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x106ccd [0x48, 0x89, 0x73, 0x0D] (StorePre 0x106ccd 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x106ccd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106ccd 6 (.base 3 (.d8 0xd)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106ccd 6 (.base 3 (.d8 0xd))).toInstrSpec (mov_m64_r64_effect_step 0x106ccd 0x48 (by decide) 6 (.base 3 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x106cd1 [0x48, 0x89, 0x53, 0x05] (StorePre 0x106cd1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x106cd1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106cd1 2 (.base 3 (.d8 0x5)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106cd1 2 (.base 3 (.d8 0x5))).toInstrSpec (mov_m64_r64_effect_step 0x106cd1 0x48 (by decide) 2 (.base 3 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x106cd5 [0x89, 0x03] (StorePre 0x106cd5 2 (fun s => AddrMode.addr (.base 3 .none) s (0x106cd5 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x106cd5 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106cd5 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x106cd5 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x106cd7 [0x88, 0x4B, 0x04] (StorePre 0x106cd7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106cd7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x106cd7 3 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x106cd7 3 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x106cd7 1 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c9c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c9f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ca4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ca8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cad) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cb1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cb6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cba) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cbf) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cc3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cc8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ccd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cd1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cd5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cd7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cda) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 76) (jmp_rel32_effect_step 0x106cda 0x8c (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106c98 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106c98 :=
  Rest.liftedBlock (rest_l106c98 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106c98 x hx)

theorem rest_l106cdf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106cdf bytes_l106cdf) (entryMap (live .l106cdf))
      3 0x106cdf bytes_l106cdf b_l106cdf := by
  have f0 : InstrSpec 0x106cdf [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106cdf) (leaR64Effect 0x106cdf 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106cdf 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106cdf 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106ce4 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x106ce4) (movR64R64Effect 0x106ce4 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x106ce4 6 14).toInstrSpec (mov_r64_r64_effect_step 0x106ce4 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106ce7 [0xE8, 0x74, 0xFB, 0xFF, 0xFF] (PushPre 0x106ce7 5) (callEffect (fun _ => 0x106860) 0x106cec)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106ce7 0x106860 0x106cec).toInstrSpec (call_rel32_effect_step 0x106ce7 0xfffffb74 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ce4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ce7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106860) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l106cdf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106cdf :=
  Rest.liftedBlock (rest_l106cdf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106cdf x hx)

theorem rest_l106cec [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106cec bytes_l106cec) (entryMap (live .l106cec))
      4 0x106cec bytes_l106cec b_l106cec := by
  have f0 : InstrSpec 0x106cec [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x106cec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106cec + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106cec 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106cec 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x106cec 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106cf0 [0x0F, 0xB6, 0x4C, 0x24, 0x0C] (LoadPre 0x106cf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106cf0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106cf0 5 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x106cf0 5 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x106cf0 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106cf5 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x106cf5) (cmpR32Imm8Effect 0x106cf5 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106cf5 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106cf5 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cf0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cf5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cf8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x106cf8 5 0x9e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106cec [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106cec :=
  Rest.liftedBlock (rest_l106cec code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106cec x hx)

theorem rest_l106cfa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106cfa bytes_l106cfa) (entryMap (live .l106cfa))
      7 0x106cfa bytes_l106cfa b_l106cfa := by
  have f0 : InstrSpec 0x106cfa [0x0F, 0xB6, 0xC1] (fun s => s.RIP = 0x106cfa) (movzxR32R8Effect 0x106cfa 3 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x106cfa 3 0 1).toInstrSpec (movzx_r32_r8_effect_step 0x106cfa 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106cfd [0x41, 0xC1, 0xE4, 0x07] (fun s => s.RIP = 0x106cfd) (shlR32Effect 0x106cfd 4 12 7)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x106cfd 4 12 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x106cfd 0x41 0xe4 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106d01 [0x41, 0x89, 0xC5] (fun s => s.RIP = 0x106d01) (movR32R32Effect 0x106d01 3 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x106d01 3 13 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x106d01 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106d04 [0x41, 0x83, 0xE5, 0x7F] (fun s => s.RIP = 0x106d04) (andR32Imm8Effect 0x106d04 4 13 0x7f)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x106d04 4 13 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x106d04 0x41 0xe5 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106d08 [0x45, 0x09, 0xE5] (fun s => s.RIP = 0x106d08) (orR32R32Effect 0x106d08 3 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106d08 3 13 12).toInstrSpec (or_r32_r32_rex_effect_step 0x106d08 0x45 0xe5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x106d0b [0x84, 0xC0] (fun s => s.RIP = 0x106d0b) (testR8R8Effect 0x106d0b 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x106d0b 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x106d0b 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cfd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d01) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d04) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d08) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d0b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 61), (14, 14), (15, 15), (20, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d0d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x106d0d 8 0x8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106cfa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106cfa :=
  Rest.liftedBlock (rest_l106cfa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106cfa x hx)

theorem rest_l106d0f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d0f bytes_l106d0f) (entryMap (live .l106d0f))
      2 0x106d0f bytes_l106d0f b_l106d0f := by
  have f0 : InstrSpec 0x106d0f [0x45, 0x89, 0xEF] (fun s => s.RIP = 0x106d0f) (movR32R32Effect 0x106d0f 3 15 13)
      [.gpr 13] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x106d0f 3 15 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x106d0f 0x45 0xef (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d12) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x106d12 0xfffffeb9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106d0f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d0f :=
  Rest.liftedBlock (rest_l106d0f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d0f x hx)

theorem rest_l106d17 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d17 bytes_l106d17) (entryMap (live .l106d17))
      3 0x106d17 bytes_l106d17 b_l106d17 := by
  have f0 : InstrSpec 0x106d17 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106d17) (leaR64Effect 0x106d17 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106d17 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106d17 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106d1c [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x106d1c) (movR64R64Effect 0x106d1c 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x106d1c 6 14).toInstrSpec (mov_r64_r64_effect_step 0x106d1c 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106d1f [0xE8, 0x3C, 0xFB, 0xFF, 0xFF] (PushPre 0x106d1f 5) (callEffect (fun _ => 0x106860) 0x106d24)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106d1f 0x106860 0x106d24).toInstrSpec (call_rel32_effect_step 0x106d1f 0xfffffb3c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d1c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d1f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106860) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l106d17 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d17 :=
  Rest.liftedBlock (rest_l106d17 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d17 x hx)

theorem rest_l106d24 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d24 bytes_l106d24) (entryMap (live .l106d24))
      4 0x106d24 bytes_l106d24 b_l106d24 := by
  have f0 : InstrSpec 0x106d24 [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x106d24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106d24 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106d24 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106d24 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x106d24 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106d28 [0x0F, 0xB6, 0x4C, 0x24, 0x0C] (LoadPre 0x106d28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106d28 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106d28 5 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x106d28 5 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x106d28 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106d2d [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x106d2d) (cmpR32Imm8Effect 0x106d2d 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106d2d 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106d2d 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d28) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d30) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x106d30 5 0xffffff62) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106d24 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d24 :=
  Rest.liftedBlock (rest_l106d24 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d24 x hx)

theorem rest_l106d36 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d36 bytes_l106d36) (entryMap (live .l106d36))
      7 0x106d36 bytes_l106d36 b_l106d36 := by
  have f0 : InstrSpec 0x106d36 [0x0F, 0xB6, 0xC1] (fun s => s.RIP = 0x106d36) (movzxR32R8Effect 0x106d36 3 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x106d36 3 0 1).toInstrSpec (movzx_r32_r8_effect_step 0x106d36 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106d39 [0x41, 0xC1, 0xE5, 0x07] (fun s => s.RIP = 0x106d39) (shlR32Effect 0x106d39 4 13 7)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x106d39 4 13 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x106d39 0x41 0xe5 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106d3d [0x41, 0x89, 0xC4] (fun s => s.RIP = 0x106d3d) (movR32R32Effect 0x106d3d 3 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x106d3d 3 12 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x106d3d 0x41 0xc4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106d40 [0x41, 0x83, 0xE4, 0x7F] (fun s => s.RIP = 0x106d40) (andR32Imm8Effect 0x106d40 4 12 0x7f)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x106d40 4 12 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x106d40 0x41 0xe4 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106d44 [0x45, 0x09, 0xEC] (fun s => s.RIP = 0x106d44) (orR32R32Effect 0x106d44 3 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106d44 3 12 13).toInstrSpec (or_r32_r32_rex_effect_step 0x106d44 0x45 0xec (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x106d47 [0x84, 0xC0] (fun s => s.RIP = 0x106d47) (testR8R8Effect 0x106d47 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x106d47 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x106d47 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d39) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d3d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d40) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d44) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d47) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 55), (14, 14), (15, 15), (20, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d49) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel32_effect_step 0x106d49 9 0xfffffefd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106d36 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d36 :=
  Rest.liftedBlock (rest_l106d36 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d36 x hx)

theorem rest_l106d4f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d4f bytes_l106d4f) (entryMap (live .l106d4f))
      2 0x106d4f bytes_l106d4f b_l106d4f := by
  have f0 : InstrSpec 0x106d4f [0x41, 0x80, 0xFF, 0x0F] (fun s => s.RIP = 0x106d4f) (cmpR8Imm8Effect 0x106d4f 4 15 0xf)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x106d4f 4 15 0xf).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x106d4f 0x41 0xff 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x106d53 6 0x25) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106d4f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d4f :=
  Rest.liftedBlock (rest_l106d4f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d4f x hx)

theorem rest_l106d55 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d55 bytes_l106d55) (entryMap (live .l106d55))
      5 0x106d55 bytes_l106d55 b_l106d55 := by
  have f0 : InstrSpec 0x106d55 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x106d55 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x106d55 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x106d55 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x106d55 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x106d55 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x106d5a [0x41, 0x8B, 0x46, 0x1C] (LoadPre 0x106d5a (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x106d5a + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x106d5a 0 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x106d5a 0 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x106d5a 0x41 (by decide) 0 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106d5e [0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x106d5e 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106d5e + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106d5e 6 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x106d5e 6 (.base 3 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x106d5e (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x106d64 [0x89, 0x43, 0x04] (StorePre 0x106d64 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106d64 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106d64 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106d64 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x106d64 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106d67 [0xC6, 0x43, 0x08, 0x10] (StorePre 0x106d67 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106d67 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x106d67 (.base 3 (.d8 0x8)) 0x10)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x106d67 (.base 3 (.d8 0x8)) 0x10).toInstrSpec (mov_m8_imm8_effect_step 0x106d67 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x10) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d5a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d5e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d64) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d67) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d6b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l106d55 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d55 :=
  Rest.liftedBlock (rest_l106d55 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d55 x hx)

theorem rest_l106d6b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d6b bytes_l106d6b) (entryMap (live .l106d6b))
      8 0x106d6b bytes_l106d6b b_l106d6b := by
  have f0 : InstrSpec 0x106d6b [0x48, 0x83, 0xC4, 0x78] (fun s => s.RIP = 0x106d6b) (addR64Imm8Effect 0x106d6b 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x106d6b 4 0x78).toInstrSpec (add_r64_imm8_effect_step 0x106d6b 0x48 0xc4 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106d6f [0x5B] (PopPre 0x106d6f) (popR64Effect 0x106d6f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106d6f 1 3).toInstrSpec (pop_r64_effect_step 0x106d6f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x106d70 [0x41, 0x5C] (PopPre 0x106d70) (popR64Effect 0x106d70 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106d70 2 12).toInstrSpec (pop_r64_rex_effect_step 0x106d70 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106d72 [0x41, 0x5D] (PopPre 0x106d72) (popR64Effect 0x106d72 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106d72 2 13).toInstrSpec (pop_r64_rex_effect_step 0x106d72 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x106d74 [0x41, 0x5E] (PopPre 0x106d74) (popR64Effect 0x106d74 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106d74 2 14).toInstrSpec (pop_r64_rex_effect_step 0x106d74 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x106d76 [0x41, 0x5F] (PopPre 0x106d76) (popR64Effect 0x106d76 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106d76 2 15).toInstrSpec (pop_r64_rex_effect_step 0x106d76 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x106d78 [0x5D] (PopPre 0x106d78) (popR64Effect 0x106d78 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106d78 1 5).toInstrSpec (pop_r64_effect_step 0x106d78 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x106d79 [0xC3] (RetPre 0x106d79) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x106d79).toInstrSpec (ret_effect_step 0x106d79) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d6f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d70) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d72) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d74) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d76) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d78) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d79) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l106d6b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d6b :=
  Rest.liftedBlock (rest_l106d6b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d6b x hx)

theorem rest_l106d7a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d7a bytes_l106d7a) (entryMap (live .l106d7a))
      3 0x106d7a bytes_l106d7a b_l106d7a := by
  have f0 : InstrSpec 0x106d7a [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106d7a) (leaR64Effect 0x106d7a 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106d7a 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106d7a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106d7f [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x106d7f) (movR64R64Effect 0x106d7f 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x106d7f 6 14).toInstrSpec (mov_r64_r64_effect_step 0x106d7f 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106d82 [0xE8, 0xD9, 0xFA, 0xFF, 0xFF] (PushPre 0x106d82 5) (callEffect (fun _ => 0x106860) 0x106d87)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106d82 0x106860 0x106d87).toInstrSpec (call_rel32_effect_step 0x106d82 0xfffffad9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d7f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d82) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106860) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l106d7a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d7a :=
  Rest.liftedBlock (rest_l106d7a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d7a x hx)

theorem rest_l106d87 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d87 bytes_l106d87) (entryMap (live .l106d87))
      4 0x106d87 bytes_l106d87 b_l106d87 := by
  have f0 : InstrSpec 0x106d87 [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x106d87 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106d87 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106d87 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106d87 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x106d87 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106d8b [0x0F, 0xB6, 0x4C, 0x24, 0x0C] (LoadPre 0x106d8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106d8b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106d8b 5 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x106d8b 5 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x106d8b 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106d90 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x106d90) (cmpR32Imm8Effect 0x106d90 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106d90 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106d90 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d8b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d90) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d93) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x106d93 5 0xfffffeff) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106d87 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d87 :=
  Rest.liftedBlock (rest_l106d87 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d87 x hx)

theorem rest_l106d99 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d99 bytes_l106d99) (entryMap (live .l106d99))
      2 0x106d99 bytes_l106d99 b_l106d99 := by
  have f0 : InstrSpec 0x106d99 [0x84, 0xC9] (fun s => s.RIP = 0x106d99) (testR8R8Effect 0x106d99 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x106d99 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x106d99 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (20, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d9b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x106d9b 8 0xb8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106d99 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d99 :=
  Rest.liftedBlock (rest_l106d99 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d99 x hx)

theorem rest_l106d9d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d9d bytes_l106d9d) (entryMap (live .l106d9d))
      5 0x106d9d bytes_l106d9d b_l106d9d := by
  have f0 : InstrSpec 0x106d9d [0x44, 0x0F, 0xB6, 0xF9] (fun s => s.RIP = 0x106d9d) (movzxR32R8Effect 0x106d9d 4 15 1)
      [.gpr 1] [] [.reg 15, .rip] :=
    (movzxR32R8Effect_footprint 0x106d9d 4 15 1).toInstrSpec (movzx_r32_r8_rex_effect_step 0x106d9d 0x44 (by decide) 0xf9 (by decide)) pre_rip
  have f1 : InstrSpec 0x106da1 [0x41, 0xC1, 0xE4, 0x07] (fun s => s.RIP = 0x106da1) (shlR32Effect 0x106da1 4 12 7)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x106da1 4 12 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x106da1 0x41 0xe4 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106da5 [0x41, 0x83, 0xE7, 0x7F] (fun s => s.RIP = 0x106da5) (andR32Imm8Effect 0x106da5 4 15 0x7f)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x106da5 4 15 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x106da5 0x41 0xe7 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106da9 [0x45, 0x09, 0xE7] (fun s => s.RIP = 0x106da9) (orR32R32Effect 0x106da9 3 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106da9 3 15 12).toInstrSpec (or_r32_r32_rex_effect_step 0x106da9 0x45 0xe7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106da1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106da5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106da9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dac) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel32_effect_step 0x106dac 0xfffffe1f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106d9d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d9d :=
  Rest.liftedBlock (rest_l106d9d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d9d x hx)

theorem rest_l106db1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106db1 bytes_l106db1) (entryMap (live .l106db1))
      3 0x106db1 bytes_l106db1 b_l106db1 := by
  have f0 : InstrSpec 0x106db1 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106db1) (movR32Imm32Effect 0x106db1 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x106db1 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x106db1 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x106db6 [0x48, 0xC7, 0xC2, 0x30, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x106db6) (movR64Imm32Effect 0x106db6 2 0x202530)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x106db6 2 0x202530).toInstrSpec (mov_r64_imm32_effect_step 0x106db6 0x48 0xc2 (by decide) (by decide) (by decide) 0x202530) pre_rip
  have f2 : InstrSpec 0x106dbd [0xE8, 0xCE, 0x2E, 0x02, 0x00] (PushPre 0x106dbd 5) (callEffect (fun _ => 0x129c90) 0x106dc2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106dbd 0x129c90 0x106dc2).toInstrSpec (call_rel32_effect_step 0x106dbd 0x22ece (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x106db6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x106dbd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l106db1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106db1 :=
  Rest.liftedBlock (rest_l106db1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106db1 x hx)

theorem rest_l106dc2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106dc2 bytes_l106dc2) (entryMap (live .l106dc2))
      2 0x106dc2 bytes_l106dc2 b_l106dc2 := by
  have f0 : InstrSpec 0x106dc2 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106dc2) (fun _ => nopEffect 0x106dc2 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x106dc2 10).toInstrSpec (nop_m_effect_step 0x106dc2 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106dcc [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x106dcc) (fun _ => nopEffect 0x106dcc 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x106dcc 4).toInstrSpec (nop_m_effect_step 0x106dcc [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dcc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l106dc2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106dc2 :=
  Rest.liftedBlock (rest_l106dc2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106dc2 x hx)

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

theorem_by block_l106b60_eval :
    program.runBlock (dialect code) ⟨.l106b60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106b81_eval :
    program.runBlock (dialect code) ⟨.l106b81, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106b96_eval :
    program.runBlock (dialect code) ⟨.l106b96, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106ba3_eval :
    program.runBlock (dialect code) ⟨.l106ba3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106bb2_eval :
    program.runBlock (dialect code) ⟨.l106bb2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106bc6_eval :
    program.runBlock (dialect code) ⟨.l106bc6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106bd0_eval :
    program.runBlock (dialect code) ⟨.l106bd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106bde_eval :
    program.runBlock (dialect code) ⟨.l106bde, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106bed_eval :
    program.runBlock (dialect code) ⟨.l106bed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106bf8_eval :
    program.runBlock (dialect code) ⟨.l106bf8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106c01_eval :
    program.runBlock (dialect code) ⟨.l106c01, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106c13_eval :
    program.runBlock (dialect code) ⟨.l106c13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106c1c_eval :
    program.runBlock (dialect code) ⟨.l106c1c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106c2b_eval :
    program.runBlock (dialect code) ⟨.l106c2b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106c4c_eval :
    program.runBlock (dialect code) ⟨.l106c4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106c54_eval :
    program.runBlock (dialect code) ⟨.l106c54, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106c98_eval :
    program.runBlock (dialect code) ⟨.l106c98, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106cdf_eval :
    program.runBlock (dialect code) ⟨.l106cdf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106cec_eval :
    program.runBlock (dialect code) ⟨.l106cec, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106cfa_eval :
    program.runBlock (dialect code) ⟨.l106cfa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d0f_eval :
    program.runBlock (dialect code) ⟨.l106d0f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d17_eval :
    program.runBlock (dialect code) ⟨.l106d17, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d24_eval :
    program.runBlock (dialect code) ⟨.l106d24, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d36_eval :
    program.runBlock (dialect code) ⟨.l106d36, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d4f_eval :
    program.runBlock (dialect code) ⟨.l106d4f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d55_eval :
    program.runBlock (dialect code) ⟨.l106d55, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d6b_eval :
    program.runBlock (dialect code) ⟨.l106d6b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d7a_eval :
    program.runBlock (dialect code) ⟨.l106d7a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d87_eval :
    program.runBlock (dialect code) ⟨.l106d87, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d99_eval :
    program.runBlock (dialect code) ⟨.l106d99, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d9d_eval :
    program.runBlock (dialect code) ⟨.l106d9d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106db1_eval :
    program.runBlock (dialect code) ⟨.l106db1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106dc2_eval :
    program.runBlock (dialect code) ⟨.l106dc2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
