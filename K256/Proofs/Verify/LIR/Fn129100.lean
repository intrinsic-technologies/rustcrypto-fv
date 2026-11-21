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

theorem rest_l129100 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129100 bytes_l129100) (entryMap (live .l129100))
      13 0x129100 bytes_l129100 b_l129100 := by
  have f0 : InstrSpec 0x129100 [0x55] (PushPre 0x129100 1) (pushR64Effect 0x129100 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129100 1 5).toInstrSpec (push_r64_effect_step 0x129100 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129101 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129101) (movR64R64Effect 0x129101 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129101 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129101 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129104 [0x41, 0x57] (PushPre 0x129104 2) (pushR64Effect 0x129104 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129104 2 15).toInstrSpec (push_r64_rex_effect_step 0x129104 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129106 [0x41, 0x56] (PushPre 0x129106 2) (pushR64Effect 0x129106 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129106 2 14).toInstrSpec (push_r64_rex_effect_step 0x129106 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x129108 [0x41, 0x55] (PushPre 0x129108 2) (pushR64Effect 0x129108 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129108 2 13).toInstrSpec (push_r64_rex_effect_step 0x129108 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x12910a [0x41, 0x54] (PushPre 0x12910a 2) (pushR64Effect 0x12910a 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12910a 2 12).toInstrSpec (push_r64_rex_effect_step 0x12910a 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12910c [0x53] (PushPre 0x12910c 1) (pushR64Effect 0x12910c 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12910c 1 3).toInstrSpec (push_r64_effect_step 0x12910c 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x12910d [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x12910d) (subR64Imm8Effect 0x12910d 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x12910d 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x12910d 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129111 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x129111) (movR64R64Effect 0x129111 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x129111 13 2).toInstrSpec (mov_r64_r64_effect_step 0x129111 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129114 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x129114) (movR64R64Effect 0x129114 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x129114 14 6).toInstrSpec (mov_r64_r64_effect_step 0x129114 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129117 [0x44, 0x8B, 0x7F, 0x10] (LoadPre 0x129117 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x129117 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x129117 15 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x129117 15 (.base 7 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x129117 0x44 (by decide) 7 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x12911b [0x41, 0xF7, 0xC7, 0x00, 0x00, 0x00, 0x18] (fun s => s.RIP = 0x12911b) (testR32Imm32Effect 0x12911b 7 15 0x18000000)
      [.gpr 15] [] [.flags, .rip] :=
    (testR32Imm32Effect_footprint 0x12911b 7 15 0x18000000).toInstrSpec (test_r32_imm32_rex_effect_step 0x12911b 0x41 0xc7 0x18000000 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129101) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129104) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129106) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129108) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12910a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12910c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12910d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129111) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129114) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129117) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12911b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 71), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129122) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel32_effect_step 0x129122 4 0x183) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129100 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129100 :=
  Rest.liftedBlock (rest_l129100 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129100 x hx)

theorem rest_l129128 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129128 bytes_l129128) (entryMap (live .l129128))
      2 0x129128 bytes_l129128 b_l129128 := by
  have f0 : InstrSpec 0x129128 [0x41, 0xF7, 0xC7, 0x00, 0x00, 0x00, 0x10] (fun s => s.RIP = 0x129128) (testR32Imm32Effect 0x129128 7 15 0x10000000)
      [.gpr 15] [] [.flags, .rip] :=
    (testR32Imm32Effect_footprint 0x129128 7 15 0x10000000).toInstrSpec (test_r32_imm32_rex_effect_step 0x129128 0x41 0xc7 0x10000000 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12912f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12912f 5 0x2d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129128 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129128 :=
  Rest.liftedBlock (rest_l129128 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129128 x hx)

theorem rest_l129131 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129131 bytes_l129131) (entryMap (live .l129131))
      2 0x129131 bytes_l129131 b_l129131 := by
  have f0 : InstrSpec 0x129131 [0x49, 0x83, 0xFD, 0x20] (fun s => s.RIP = 0x129131) (cmpR64Imm8Effect 0x129131 13 0x20)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x129131 13 0x20).toInstrSpec (cmp_r64_imm8_effect_step 0x129131 0x49 0xfd 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129135) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x129135 3 0x84) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129131 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129131 :=
  Rest.liftedBlock (rest_l129131 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129131 x hx)

theorem rest_l12913b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12913b bytes_l12913b) (entryMap (live .l12913b))
      2 0x12913b bytes_l12913b b_l12913b := by
  have f0 : InstrSpec 0x12913b [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x12913b) (testR64R64Effect 0x12913b 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12913b 13 13).toInstrSpec (test_r64_r64_effect_step 0x12913b 0x4d 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)]) (p' := 0x12913e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x12913e 4 0xa9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12913b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12913b :=
  Rest.liftedBlock (rest_l12913b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12913b x hx)

theorem rest_l129144 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129144 bytes_l129144) (entryMap (live .l129144))
      4 0x129144 bytes_l129144 b_l129144 := by
  have f0 : InstrSpec 0x129144 [0x44, 0x89, 0xE8] (fun s => s.RIP = 0x129144) (movR32R32Effect 0x129144 3 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x129144 3 0 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x129144 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129147 [0x83, 0xE0, 0x03] (fun s => s.RIP = 0x129147) (andR32Imm8Effect 0x129147 3 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x129147 3 0 0x3).toInstrSpec (and_r32_imm8_effect_step 0x129147 0xe0 0x3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12914a [0x49, 0x83, 0xFD, 0x04] (fun s => s.RIP = 0x12914a) (cmpR64Imm8Effect 0x12914a 13 0x4)
      [.gpr 13] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12914a 13 0x4).toInstrSpec (cmp_r64_imm8_effect_step 0x12914a 0x49 0xfd 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129147) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x12914a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57)]) (p' := 0x12914e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x12914e 3 0xa1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129144 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129144 :=
  Rest.liftedBlock (rest_l129144 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129144 x hx)

theorem rest_l129154 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129154 bytes_l129154) (entryMap (live .l129154))
      3 0x129154 bytes_l129154 b_l129154 := by
  have f0 : InstrSpec 0x129154 [0x31, 0xC9] (fun s => s.RIP = 0x129154) (xorR32R32Effect 0x129154 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129154 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x129154 0xc9 (by decide)) pre_rip
  have f1 : InstrSpec 0x129156 [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x129156) (xorR32R32Effect 0x129156 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129156 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x129156 0x45 0xe4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129156) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 55), (13, 13), (14, 14), (15, 15)]) (p' := 0x129159) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x129159 0xee (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129154 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129154 :=
  Rest.liftedBlock (rest_l129154 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129154 x hx)

theorem rest_l12915e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12915e bytes_l12915e) (entryMap (live .l12915e))
      3 0x12915e bytes_l12915e b_l12915e := by
  have f0 : InstrSpec 0x12915e [0x44, 0x0F, 0xB7, 0x67, 0x16] (LoadPre 0x12915e (fun s => AddrMode.addr (.base 7 (.d8 0x16)) s (0x12915e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x12915e 5 12 (.base 7 (.d8 0x16)))
      [.gpr 7] [] [.reg 12, .rip] :=
    (movzxR32M16Effect_footprint 0x12915e 5 12 (.base 7 (.d8 0x16))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x12915e 0x44 (by decide) 4 (.base 7 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129163 [0x4D, 0x85, 0xE4] (fun s => s.RIP = 0x129163) (testR64R64Effect 0x129163 12 12)
      [.gpr 12, .gpr 12] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x129163 12 12).toInstrSpec (test_r64_r64_effect_step 0x129163 0x4d 0xe4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (7, 7), (12, 53), (13, 13), (14, 14), (15, 15)]) (p' := 0x129163) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (7, 7), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55)]) (p' := 0x129166) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x129166 4 0x71) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12915e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12915e :=
  Rest.liftedBlock (rest_l12915e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12915e x hx)

theorem rest_l129168 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129168 bytes_l129168) (entryMap (live .l129168))
      5 0x129168 bytes_l129168 b_l129168 := by
  have f0 : InstrSpec 0x129168 [0x4D, 0x01, 0xF5] (fun s => s.RIP = 0x129168) (addR64R64Effect 0x129168 13 14)
      [.gpr 13, .gpr 14] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129168 13 14).toInstrSpec (add_r64_r64_effect_step 0x129168 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12916b [0x31, 0xD2] (fun s => s.RIP = 0x12916b) (xorR32R32Effect 0x12916b 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12916b 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x12916b 0xd2 (by decide)) pre_rip
  have f2 : InstrSpec 0x12916d [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x12916d) (movR64R64Effect 0x12916d 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12916d 1 14).toInstrSpec (mov_r64_r64_effect_step 0x12916d 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129170 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x129170) (movR64R64Effect 0x129170 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x129170 0 12).toInstrSpec (mov_r64_r64_effect_step 0x129170 0x4c 0xe0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (5, 5), (7, 7), (12, 12), (13, 53), (14, 14), (15, 15)]) (p' := 0x12916b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (7, 7), (12, 12), (13, 53), (14, 14), (15, 15)]) (p' := 0x12916d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (4, 4), (5, 5), (7, 7), (12, 12), (13, 53), (14, 14), (15, 15)]) (p' := 0x129170) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 57), (2, 55), (4, 4), (5, 5), (7, 7), (12, 12), (13, 53), (14, 14), (15, 15)]) (p' := 0x129173) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel8_effect_step 0x129173 0x20 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129168 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129168 :=
  Rest.liftedBlock (rest_l129168 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129168 x hx)

theorem rest_l129180 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129180 bytes_l129180) (entryMap (live .l129180))
      1 0x129180 bytes_l129180 b_l129180 := by
  have f0 : InstrSpec 0x129180 [0x4C, 0x8D, 0x41, 0x01] (fun s => s.RIP = 0x129180) (leaR64Effect 0x129180 8 (.base 1 (.d8 0x1)))
      [.gpr 1] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x129180 8 (.base 1 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x129180 0x4c (by decide) 0 (.base 1 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129184) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l129180 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129180 :=
  Rest.liftedBlock (rest_l129180 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129180 x hx)

theorem rest_l129184 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129184 bytes_l129184) (entryMap (live .l129184))
      6 0x129184 bytes_l129184 b_l129184 := by
  have f0 : InstrSpec 0x129184 [0x4C, 0x89, 0xC2] (fun s => s.RIP = 0x129184) (movR64R64Effect 0x129184 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129184 2 8).toInstrSpec (mov_r64_r64_effect_step 0x129184 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129187 [0x48, 0x29, 0xCA] (fun s => s.RIP = 0x129187) (subR64R64Effect 0x129187 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x129187 2 1).toInstrSpec (sub_r64_r64_effect_step 0x129187 0x48 0xca (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12918a [0x48, 0x01, 0xF2] (fun s => s.RIP = 0x12918a) (addR64R64Effect 0x12918a 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12918a 2 6).toInstrSpec (add_r64_r64_effect_step 0x12918a 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12918d [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x12918d) (movR64R64Effect 0x12918d 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12918d 1 8).toInstrSpec (mov_r64_r64_effect_step 0x12918d 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129190 [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x129190) (decR64Effect 0x129190 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x129190 0).toInstrSpec (dec_r64_effect_step 0x129190 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129187) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x12918a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x12918d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129190) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 62) f4 .ZF (fun _ => rfl) (decR64Effect_fresh 0x129190 0 _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 59), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62)]) (p' := 0x129193) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel8_effect_step 0x129193 4 0x46) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129184 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129184 :=
  Rest.liftedBlock (rest_l129184 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129184 x hx)

theorem rest_l129195 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129195 bytes_l129195) (entryMap (live .l129195))
      3 0x129195 bytes_l129195 b_l129195 := by
  have f0 : InstrSpec 0x129195 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x129195) (movR64R64Effect 0x129195 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x129195 6 2).toInstrSpec (mov_r64_r64_effect_step 0x129195 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129198 [0x4C, 0x39, 0xE9] (fun s => s.RIP = 0x129198) (cmpR64R64Effect 0x129198 1 13)
      [.gpr 1, .gpr 13] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129198 1 13).toInstrSpec (cmp_r64_r64_effect_step 0x129198 0x4c 0xe9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129198) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55)]) (p' := 0x12919b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12919b 4 0x42) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129195 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129195 :=
  Rest.liftedBlock (rest_l129195 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129195 x hx)

theorem rest_l12919d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12919d bytes_l12919d) (entryMap (live .l12919d))
      3 0x12919d bytes_l12919d b_l12919d := by
  have f0 : InstrSpec 0x12919d [0x0F, 0xB6, 0x11] (LoadPre 0x12919d (fun s => AddrMode.addr (.base 1 .none) s (0x12919d + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x12919d 3 2 (.base 1 .none))
      [.gpr 1] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x12919d 3 2 (.base 1 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x12919d 2 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1291a0 [0x84, 0xD2] (fun s => s.RIP = 0x1291a0) (testR8R8Effect 0x1291a0 2 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1291a0 2 2 2).toInstrSpec (test_r8_r8_effect_step 0x1291a0 0xd2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55)]) (p' := 0x1291a2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1291a2 9 0xdc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12919d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12919d :=
  Rest.liftedBlock (rest_l12919d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12919d x hx)

theorem rest_l1291a4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291a4 bytes_l1291a4) (entryMap (live .l1291a4))
      2 0x1291a4 bytes_l1291a4 b_l1291a4 := by
  have f0 : InstrSpec 0x1291a4 [0x80, 0xFA, 0xE0] (fun s => s.RIP = 0x1291a4) (cmpR8Imm8Effect 0x1291a4 3 2 0xe0)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1291a4 3 2 0xe0).toInstrSpec (cmp_r8_imm8_effect_step 0x1291a4 0xfa 0xe0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53)]) (p' := 0x1291a7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1291a7 2 0x10) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1291a4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291a4 :=
  Rest.liftedBlock (rest_l1291a4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291a4 x hx)

theorem rest_l1291a9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291a9 bytes_l1291a9) (entryMap (live .l1291a9))
      5 0x1291a9 bytes_l1291a9 b_l1291a9 := by
  have f0 : InstrSpec 0x1291a9 [0x80, 0xFA, 0xF0] (fun s => s.RIP = 0x1291a9) (cmpR8Imm8Effect 0x1291a9 3 2 0xf0)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1291a9 3 2 0xf0).toInstrSpec (cmp_r8_imm8_effect_step 0x1291a9 0xfa 0xf0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1291ac [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x1291ac) (movR64R64Effect 0x1291ac 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1291ac 8 1).toInstrSpec (mov_r64_r64_effect_step 0x1291ac 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1291af [0x49, 0x83, 0xD8, 0xFF] (fun s => s.RIP = 0x1291af) (atFlags StatusFlags.CF (sbbR64Imm8Effect 0x1291af 8 0xff))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (sbbR64Imm8Effect_footprint 0x1291af 8 0xff).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_imm8_effect_step 0x1291af 0x49 0xd8 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f3 : InstrSpec 0x1291b3 [0x49, 0x83, 0xC0, 0x03] (fun s => s.RIP = 0x1291b3) (addR64Imm8Effect 0x1291b3 8 0x3)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1291b3 8 0x3).toInstrSpec (add_r64_imm8_effect_step 0x1291b3 0x49 0xc0 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53)]) (p' := 0x1291ac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53)]) (p' := 0x1291af) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291b3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291b7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel8_effect_step 0x1291b7 0xcb (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1291a9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291a9 :=
  Rest.liftedBlock (rest_l1291a9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291a9 x hx)

theorem rest_l1291b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291b9 bytes_l1291b9) (entryMap (live .l1291b9))
      2 0x1291b9 bytes_l1291b9 b_l1291b9 := by
  have f0 : InstrSpec 0x1291b9 [0x4C, 0x8D, 0x41, 0x02] (fun s => s.RIP = 0x1291b9) (leaR64Effect 0x1291b9 8 (.base 1 (.d8 0x2)))
      [.gpr 1] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1291b9 8 (.base 1 (.d8 0x2))).toInstrSpec (lea_r64_effect_step 0x1291b9 0x4c (by decide) 0 (.base 1 (.d8 0x2)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291bd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x1291bd 0xc5 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1291b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291b9 :=
  Rest.liftedBlock (rest_l1291b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291b9 x hx)

theorem rest_l1291bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291bf bytes_l1291bf) (entryMap (live .l1291bf))
      4 0x1291bf bytes_l1291bf b_l1291bf := by
  have f0 : InstrSpec 0x1291bf [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1291bf) (movR64R64Effect 0x1291bf 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1291bf 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1291bf 0x48 0xfb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1291c2 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1291c2) (movR64R64Effect 0x1291c2 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1291c2 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1291c2 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1291c5 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x1291c5) (movR64R64Effect 0x1291c5 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1291c5 6 13).toInstrSpec (mov_r64_r64_effect_step 0x1291c5 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1291c8 [0xFF, 0x15, 0x22, 0xAC, 0x0D, 0x00] (GoesTo (CallMemPre 0x1291c8 (.rip 0xdac22)) (callEffect (callMemPtr 0x1291c8 (.rip 0xdac22)) (0x1291c8 + BitVec.ofNat 64 (callMemLen (.rip 0xdac22)))) 0x1297a0) (callEffect (callMemPtr 0x1291c8 (.rip 0xdac22)) (0x1291c8 + BitVec.ofNat 64 (callMemLen (.rip 0xdac22))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1291c8 (.rip 0xdac22)).toInstrSpec (call_m64_effect_step 0x1291c8 (.rip 0xdac22) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x1297a0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 53), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1291c2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 53), (4, 4), (5, 5), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1291c5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 53), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1291c8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 53), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297a0) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1291bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291bf :=
  Rest.liftedBlock (rest_l1291bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291bf x hx)

theorem rest_l1291ce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291ce bytes_l1291ce) (entryMap (live .l1291ce))
      3 0x1291ce bytes_l1291ce b_l1291ce := by
  have f0 : InstrSpec 0x1291ce [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1291ce) (movR64R64Effect 0x1291ce 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1291ce 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1291ce 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1291d1 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x1291d1) (movR64R64Effect 0x1291d1 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1291d1 12 0).toInstrSpec (mov_r64_r64_effect_step 0x1291d1 0x49 0xc4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 53), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291d1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 53), (12, 55), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291d4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x1291d4 0x9c (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1291ce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291ce :=
  Rest.liftedBlock (rest_l1291ce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291ce x hx)

theorem rest_l1291d9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291d9 bytes_l1291d9) (entryMap (live .l1291d9))
      1 0x1291d9 bytes_l1291d9 b_l1291d9 := by
  have f0 : InstrSpec 0x1291d9 [0x31, 0xD2] (fun s => s.RIP = 0x1291d9) (xorR32R32Effect 0x1291d9 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1291d9 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x1291d9 0xd2 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (7, 7), (12, 12), (14, 14), (15, 15)]) (p' := 0x1291db) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1291d9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291d9 :=
  Rest.liftedBlock (rest_l1291d9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291d9 x hx)

theorem rest_l1291db [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291db bytes_l1291db) (entryMap (live .l1291db))
      2 0x1291db bytes_l1291db b_l1291db := by
  have f0 : InstrSpec 0x1291db [0x31, 0xC0] (fun s => s.RIP = 0x1291db) (xorR32R32Effect 0x1291db 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1291db 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1291db 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (7, 7), (12, 12), (14, 14), (15, 15)]) (p' := 0x1291dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x1291dd 0x3 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1291db [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291db :=
  Rest.liftedBlock (rest_l1291db code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291db x hx)

theorem rest_l1291df [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291df bytes_l1291df) (entryMap (live .l1291df))
      1 0x1291df bytes_l1291df b_l1291df := by
  have f0 : InstrSpec 0x1291df [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x1291df) (movR64R64Effect 0x1291df 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1291df 2 6).toInstrSpec (mov_r64_r64_effect_step 0x1291df 0x48 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (14, 14), (15, 15)]) (p' := 0x1291e2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1291df [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291df :=
  Rest.liftedBlock (rest_l1291df code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291df x hx)

theorem rest_l1291e2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291e2 bytes_l1291e2) (entryMap (live .l1291e2))
      3 0x1291e2 bytes_l1291e2 b_l1291e2 := by
  have f0 : InstrSpec 0x1291e2 [0x49, 0x29, 0xC4] (fun s => s.RIP = 0x1291e2) (subR64R64Effect 0x1291e2 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1291e2 12 0).toInstrSpec (sub_r64_r64_effect_step 0x1291e2 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1291e5 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x1291e5) (movR64R64Effect 0x1291e5 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1291e5 13 2).toInstrSpec (mov_r64_r64_effect_step 0x1291e5 0x49 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (7, 7), (12, 53), (14, 14), (15, 15)]) (p' := 0x1291e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (7, 7), (12, 53), (13, 55), (14, 14), (15, 15)]) (p' := 0x1291e8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x1291e8 0x88 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1291e2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291e2 :=
  Rest.liftedBlock (rest_l1291e2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291e2 x hx)

theorem rest_l1291ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291ed bytes_l1291ed) (entryMap (live .l1291ed))
      2 0x1291ed bytes_l1291ed b_l1291ed := by
  have f0 : InstrSpec 0x1291ed [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x1291ed) (xorR32R32Effect 0x1291ed 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1291ed 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x1291ed 0x45 0xe4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 7), (12, 53), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291f0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1291f0 0x80 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1291ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291ed :=
  Rest.liftedBlock (rest_l1291ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291ed x hx)

theorem rest_l1291f5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1291f5 bytes_l1291f5) (entryMap (live .l1291f5))
      4 0x1291f5 bytes_l1291f5 b_l1291f5 := by
  have f0 : InstrSpec 0x1291f5 [0x44, 0x89, 0xEA] (fun s => s.RIP = 0x1291f5) (movR32R32Effect 0x1291f5 3 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1291f5 3 2 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x1291f5 0x44 0xea (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1291f8 [0x83, 0xE2, 0x1C] (fun s => s.RIP = 0x1291f8) (andR32Imm8Effect 0x1291f8 3 2 0x1c)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1291f8 3 2 0x1c).toInstrSpec (and_r32_imm8_effect_step 0x1291f8 0xe2 0x1c (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1291fb [0x31, 0xC9] (fun s => s.RIP = 0x1291fb) (xorR32R32Effect 0x1291fb 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1291fb 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1291fb 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x1291fd [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x1291fd) (xorR32R32Effect 0x1291fd 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1291fd 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x1291fd 0x45 0xe4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291fb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x1291fd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 59), (13, 13), (14, 14), (15, 15)]) (p' := 0x129200) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l1291f5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1291f5 :=
  Rest.liftedBlock (rest_l1291f5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1291f5 x hx)

theorem rest_l129200 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129200 bytes_l129200) (entryMap (live .l129200))
      19 0x129200 bytes_l129200 b_l129200 := by
  have f0 : InstrSpec 0x129200 [0x31, 0xF6] (fun s => s.RIP = 0x129200) (xorR32R32Effect 0x129200 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129200 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x129200 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x129202 [0x41, 0x80, 0x3C, 0x0E, 0xC0] (LoadPre 0x129202 (fun s => AddrMode.addr (.sib 14 (some 1) 0 .none) s (0x129202 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129202 5 (.sib 14 (some 1) 0 .none) 0xc0)
      [.gpr 14, .gpr 1] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129202 5 (.sib 14 (some 1) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x129202 0x41 (by decide) (.sib 14 (some 1) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129207 [0x40, 0x0F, 0x9D, 0xC6] (fun s => s.RIP = 0x129207) (atFlags (condHolds 13) (setccR8Effect 0x129207 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x129207 4 6 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129207 13 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x12920b [0x4C, 0x01, 0xE6] (fun s => s.RIP = 0x12920b) (addR64R64Effect 0x12920b 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12920b 6 12).toInstrSpec (add_r64_r64_effect_step 0x12920b 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12920e [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x12920e) (xorR32R32Effect 0x12920e 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12920e 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x12920e 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129211 [0x41, 0x80, 0x7C, 0x0E, 0x01, 0xC0] (LoadPre 0x129211 (fun s => AddrMode.addr (.sib 14 (some 1) 0 (.d8 0x1)) s (0x129211 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x129211 6 (.sib 14 (some 1) 0 (.d8 0x1)) 0xc0)
      [.gpr 14, .gpr 1] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129211 6 (.sib 14 (some 1) 0 (.d8 0x1)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x129211 0x41 (by decide) (.sib 14 (some 1) 0 (.d8 0x1)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x129217 [0x41, 0x0F, 0x9D, 0xC0] (fun s => s.RIP = 0x129217) (atFlags (condHolds 13) (setccR8Effect 0x129217 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x129217 4 8 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129217 13 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x12921b [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x12921b) (xorR32R32Effect 0x12921b 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12921b 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x12921b 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12921e [0x41, 0x80, 0x7C, 0x0E, 0x02, 0xC0] (LoadPre 0x12921e (fun s => AddrMode.addr (.sib 14 (some 1) 0 (.d8 0x2)) s (0x12921e + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x12921e 6 (.sib 14 (some 1) 0 (.d8 0x2)) 0xc0)
      [.gpr 14, .gpr 1] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x12921e 6 (.sib 14 (some 1) 0 (.d8 0x2)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x12921e 0x41 (by decide) (.sib 14 (some 1) 0 (.d8 0x2)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x129224 [0x41, 0x0F, 0x9D, 0xC1] (fun s => s.RIP = 0x129224) (atFlags (condHolds 13) (setccR8Effect 0x129224 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x129224 4 9 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129224 13 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x129228 [0x4D, 0x01, 0xC1] (fun s => s.RIP = 0x129228) (addR64R64Effect 0x129228 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129228 9 8).toInstrSpec (add_r64_r64_effect_step 0x129228 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12922b [0x49, 0x01, 0xF1] (fun s => s.RIP = 0x12922b) (addR64R64Effect 0x12922b 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12922b 9 6).toInstrSpec (add_r64_r64_effect_step 0x12922b 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x12922e [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x12922e) (xorR32R32Effect 0x12922e 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12922e 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x12922e 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x129231 [0x41, 0x80, 0x7C, 0x0E, 0x03, 0xC0] (LoadPre 0x129231 (fun s => AddrMode.addr (.sib 14 (some 1) 0 (.d8 0x3)) s (0x129231 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x129231 6 (.sib 14 (some 1) 0 (.d8 0x3)) 0xc0)
      [.gpr 14, .gpr 1] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129231 6 (.sib 14 (some 1) 0 (.d8 0x3)) 0xc0).toInstrSpec (cmp_m8_imm8_rex_effect_step 0x129231 0x41 (by decide) (.sib 14 (some 1) 0 (.d8 0x3)) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x129237 [0x41, 0x0F, 0x9D, 0xC4] (fun s => s.RIP = 0x129237) (atFlags (condHolds 13) (setccR8Effect 0x129237 4 12))
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 12, .rip] :=
    (setccR8Effect_footprint 0x129237 4 12 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129237 13 0x41 (by decide) 0xc4 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x12923b [0x4D, 0x01, 0xCC] (fun s => s.RIP = 0x12923b) (addR64R64Effect 0x12923b 12 9)
      [.gpr 12, .gpr 9] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12923b 12 9).toInstrSpec (add_r64_r64_effect_step 0x12923b 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x12923e [0x48, 0x83, 0xC1, 0x04] (fun s => s.RIP = 0x12923e) (addR64Imm8Effect 0x12923e 1 0x4)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12923e 1 0x4).toInstrSpec (add_r64_imm8_effect_step 0x12923e 0x48 0xc1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x129242 [0x48, 0x39, 0xCA] (fun s => s.RIP = 0x129242) (cmpR64R64Effect 0x129242 2 1)
      [.gpr 2, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129242 2 1).toInstrSpec (cmp_r64_r64_effect_step 0x129242 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129202) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56)]) (p' := 0x129207) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56)]) (p' := 0x12920b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x12920e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 62), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129211) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 62), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65)]) (p' := 0x129217) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (20, 64), (21, 65)]) (p' := 0x12921b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 69), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x12921e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f8 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 69), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72)]) (p' := 0x129224) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 74), (12, 12), (13, 13), (14, 14), (15, 15), (20, 71), (21, 72)]) (p' := 0x129228) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 76), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x12922b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 78), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x12922e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 78), (12, 80), (13, 13), (14, 14), (15, 15)]) (p' := 0x129231) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f13 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f13 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 78), (12, 80), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83)]) (p' := 0x129237) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f14 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 78), (12, 85), (13, 13), (14, 14), (15, 15), (20, 82), (21, 83)]) (p' := 0x12923b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 78), (12, 87), (13, 13), (14, 14), (15, 15)]) (p' := 0x12923e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 89), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 78), (12, 87), (13, 13), (14, 14), (15, 15)]) (p' := 0x129242) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 89), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 78), (12, 87), (13, 13), (14, 14), (15, 15), (19, 91)]) (p' := 0x129245) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 93) (jcc_rel8_effect_step 0x129245 5 0xb9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129200 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129200 :=
  Rest.liftedBlock (rest_l129200 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129200 x hx)

theorem rest_l129247 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129247 bytes_l129247) (entryMap (live .l129247))
      2 0x129247 bytes_l129247 b_l129247 := by
  have f0 : InstrSpec 0x129247 [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x129247) (testR64R64Effect 0x129247 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x129247 0 0).toInstrSpec (test_r64_r64_effect_step 0x129247 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)]) (p' := 0x12924a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12924a 4 0x29) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129247 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129247 :=
  Rest.liftedBlock (rest_l129247 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129247 x hx)

theorem rest_l12924c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12924c bytes_l12924c) (entryMap (live .l12924c))
      3 0x12924c bytes_l12924c b_l12924c := by
  have f0 : InstrSpec 0x12924c [0x4C, 0x01, 0xF1] (fun s => s.RIP = 0x12924c) (addR64R64Effect 0x12924c 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12924c 1 14).toInstrSpec (add_r64_r64_effect_step 0x12924c 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12924f [0x31, 0xD2] (fun s => s.RIP = 0x12924f) (xorR32R32Effect 0x12924f 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12924f 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x12924f 0xd2 (by decide)) pre_rip
  have f2 : InstrSpec 0x129251 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129251) (fun _ => nopEffect 0x129251 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129251 15).toInstrSpec (nop_m_effect_step 0x129251 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x12924f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129251) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129260) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l12924c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12924c :=
  Rest.liftedBlock (rest_l12924c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12924c x hx)

theorem rest_l129260 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129260 bytes_l129260) (entryMap (live .l129260))
      7 0x129260 bytes_l129260 b_l129260 := by
  have f0 : InstrSpec 0x129260 [0x31, 0xF6] (fun s => s.RIP = 0x129260) (xorR32R32Effect 0x129260 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129260 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x129260 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x129262 [0x80, 0x3C, 0x11, 0xC0] (LoadPre 0x129262 (fun s => AddrMode.addr (.sib 1 (some 2) 0 .none) s (0x129262 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129262 4 (.sib 1 (some 2) 0 .none) 0xc0)
      [.gpr 1, .gpr 2] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x129262 4 (.sib 1 (some 2) 0 .none) 0xc0).toInstrSpec (cmp_m8_imm8_effect_step 0x129262 (.sib 1 (some 2) 0 .none) (by decide) (by decide) (by decide) 0xc0) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129266 [0x40, 0x0F, 0x9D, 0xC6] (fun s => s.RIP = 0x129266) (atFlags (condHolds 13) (setccR8Effect 0x129266 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x129266 4 6 13).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129266 13 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f3 : InstrSpec 0x12926a [0x49, 0x01, 0xF4] (fun s => s.RIP = 0x12926a) (addR64R64Effect 0x12926a 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12926a 12 6).toInstrSpec (add_r64_r64_effect_step 0x12926a 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12926d [0x48, 0xFF, 0xC2] (fun s => s.RIP = 0x12926d) (incR64Effect 0x12926d 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (incR64Effect_footprint 0x12926d 2).toInstrSpec (inc_r64_effect_step 0x12926d 0x48 0xc2 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x129270 [0x48, 0x39, 0xD0] (fun s => s.RIP = 0x129270) (cmpR64R64Effect 0x129270 0 2)
      [.gpr 0, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129270 0 2).toInstrSpec (cmp_r64_r64_effect_step 0x129270 0x48 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129262) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56)]) (p' := 0x129266) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (21, 56)]) (p' := 0x12926a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (12, 60), (13, 13), (14, 14), (15, 15)]) (p' := 0x12926d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (4, 4), (5, 5), (6, 58), (7, 7), (12, 60), (13, 13), (14, 14), (15, 15)]) (p' := 0x129270) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 62), (4, 4), (5, 5), (6, 58), (7, 7), (12, 60), (13, 13), (14, 14), (15, 15), (19, 64)]) (p' := 0x129273) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x129273 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129260 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129260 :=
  Rest.liftedBlock (rest_l129260 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129260 x hx)

theorem rest_l129275 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129275 bytes_l129275) (entryMap (live .l129275))
      3 0x129275 bytes_l129275 b_l129275 := by
  have f0 : InstrSpec 0x129275 [0x0F, 0xB7, 0x47, 0x14] (LoadPre 0x129275 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x129275 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x129275 4 0 (.base 7 (.d8 0x14)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x129275 4 0 (.base 7 (.d8 0x14))).toInstrSpec (movzx_r32_m16_effect_step 0x129275 0 (.base 7 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129279 [0x49, 0x39, 0xC4] (fun s => s.RIP = 0x129279) (cmpR64R64Effect 0x129279 12 0)
      [.gpr 12, .gpr 0] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x129279 12 0).toInstrSpec (cmp_r64_r64_effect_step 0x129279 0x49 0xc4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)]) (p' := 0x129279) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (4, 4), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55)]) (p' := 0x12927c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12927c 3 0x2d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129275 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129275 :=
  Rest.liftedBlock (rest_l129275 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129275 x hx)

theorem rest_l12927e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12927e bytes_l12927e) (entryMap (live .l12927e))
      11 0x12927e bytes_l12927e b_l12927e := by
  have f0 : InstrSpec 0x12927e [0x48, 0x89, 0x45, 0xC0] (StorePre 0x12927e 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x12927e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12927e 0 (.base 5 (.d8 0xc0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12927e 0 (.base 5 (.d8 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x12927e 0x48 (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x129282 [0x89, 0xC2] (fun s => s.RIP = 0x129282) (movR32R32Effect 0x129282 2 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x129282 2 2 0).toInstrSpec (mov_r32_r32_effect_step 0x129282 0xc2 (by decide)) pre_rip
  have f2 : InstrSpec 0x129284 [0x44, 0x29, 0xE2] (fun s => s.RIP = 0x129284) (subR32R32Effect 0x129284 3 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (subR32R32Effect_footprint 0x129284 3 2 12).toInstrSpec (sub_r32_r32_rex_effect_step 0x129284 0x44 0xe2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129287 [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x129287) (movR32R32Effect 0x129287 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x129287 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x129287 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12928a [0xC1, 0xE8, 0x1D] (fun s => s.RIP = 0x12928a) (shrR32Effect 0x12928a 3 0 29)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x12928a 3 0 29).toInstrSpec (shr_r32_imm8_effect_step 0x12928a 0xe8 0x1d (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12928d [0x83, 0xE0, 0x03] (fun s => s.RIP = 0x12928d) (andR32Imm8Effect 0x12928d 3 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12928d 3 0 0x3).toInstrSpec (and_r32_imm8_effect_step 0x12928d 0xe0 0x3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129290 [0x48, 0x8D, 0x0D, 0xCD, 0xA8, 0x0D, 0x00] (fun s => s.RIP = 0x129290) (leaR64Effect 0x129290 1 (.rip 0xda8cd))
      [] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x129290 1 (.rip 0xda8cd)).toInstrSpec (lea_r64_effect_step 0x129290 0x48 (by decide) 1 (.rip 0xda8cd) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129297 [0x48, 0x63, 0x04, 0x81] (LoadPre 0x129297 (fun s => AddrMode.addr (.sib 1 (some 0) 2 .none) s (0x129297 + BitVec.ofNat 64 4)) 4) (movsxdR64M32Effect 0x129297 4 0 (.sib 1 (some 0) 2 .none))
      [.gpr 1, .gpr 0] [] [.reg 0, .rip] :=
    (movsxdR64M32Effect_footprint 0x129297 4 0 (.sib 1 (some 0) 2 .none)).toInstrSpec (movsxd_r64_m32_effect_step 0x129297 0x48 (by decide) 0 (.sib 1 (some 0) 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x12929b [0x48, 0x01, 0xC8] (fun s => s.RIP = 0x12929b) (addR64R64Effect 0x12929b 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12929b 0 1).toInstrSpec (add_r64_r64_effect_step 0x12929b 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12929e [0x4C, 0x89, 0x6D, 0xB0] (StorePre 0x12929e 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x12929e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12929e 13 (.base 5 (.d8 0xb0)))
      [.gpr 13, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12929e 13 (.base 5 (.d8 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x12929e 0x4c (by decide) 5 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1292a2 [0x89, 0x55, 0xCC] (StorePre 0x1292a2 3 (fun s => AddrMode.addr (.base 5 (.d8 0xcc)) s (0x1292a2 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1292a2 2 (.base 5 (.d8 0xcc)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1292a2 2 (.base 5 (.d8 0xcc))).toInstrSpec (mov_m32_r32_low_effect_step 0x1292a2 2 (.base 5 (.d8 0xcc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x129282) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 54), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x129284) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 56), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x129287) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 56), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x12928a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (2, 56), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x12928d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (2, 56), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x129290) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 64), (2, 56), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x129297) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 64), (2, 56), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x12929b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(1, 64), (2, 56), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x12929e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 64), (2, 56), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x1292a2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(1, 64), (2, 56), (5, 5), (12, 12), (13, 13), (15, 15)]) (p' := 0x1292a5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12927e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12927e :=
  Rest.liftedBlock (rest_l12927e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12927e x hx)

theorem rest_l1292ab [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1292ab bytes_l1292ab) (entryMap (live .l1292ab))
      13 0x1292ab bytes_l1292ab b_l1292ab := by
  have f0 : InstrSpec 0x1292ab [0x48, 0x8B, 0x07] (LoadPre 0x1292ab (fun s => AddrMode.addr (.base 7 .none) s (0x1292ab + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1292ab 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1292ab 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1292ab 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1292ae [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x1292ae (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1292ae + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1292ae 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1292ae 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1292ae 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1292b2 [0x48, 0x8B, 0x49, 0x18] (LoadPre 0x1292b2 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x1292b2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1292b2 1 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1292b2 1 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1292b2 0x48 (by decide) 1 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1292b6 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x1292b6) (movR64R64Effect 0x1292b6 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1292b6 7 0).toInstrSpec (mov_r64_r64_effect_step 0x1292b6 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1292b9 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1292b9) (movR64R64Effect 0x1292b9 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1292b9 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1292b9 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1292bc [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x1292bc) (movR64R64Effect 0x1292bc 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1292bc 2 13).toInstrSpec (mov_r64_r64_effect_step 0x1292bc 0x4c 0xea (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1292bf [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x1292bf) (addR64Imm8Effect 0x1292bf 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1292bf 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x1292bf 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1292c3 [0x5B] (PopPre 0x1292c3) (popR64Effect 0x1292c3 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1292c3 1 3).toInstrSpec (pop_r64_effect_step 0x1292c3 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1292c4 [0x41, 0x5C] (PopPre 0x1292c4) (popR64Effect 0x1292c4 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1292c4 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1292c4 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x1292c6 [0x41, 0x5D] (PopPre 0x1292c6) (popR64Effect 0x1292c6 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1292c6 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1292c6 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x1292c8 [0x41, 0x5E] (PopPre 0x1292c8) (popR64Effect 0x1292c8 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1292c8 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1292c8 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x1292ca [0x41, 0x5F] (PopPre 0x1292ca) (popR64Effect 0x1292ca 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1292ca 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1292ca 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x1292cc [0x5D] (PopPre 0x1292cc) (popR64Effect 0x1292cc 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1292cc 1 5).toInstrSpec (pop_r64_effect_step 0x1292cc 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (7, 7), (13, 13), (14, 14)]) (p' := 0x1292ae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (4, 4), (7, 7), (13, 13), (14, 14)]) (p' := 0x1292b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (4, 4), (7, 7), (13, 13), (14, 14)]) (p' := 0x1292b6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (4, 4), (13, 13), (14, 14)]) (p' := 0x1292b9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (4, 4), (13, 13), (14, 14)]) (p' := 0x1292bc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (4, 4), (13, 13), (14, 14)]) (p' := 0x1292bf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (4, 61), (13, 13), (14, 14)]) (p' := 0x1292c3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (4, 63), (13, 13), (14, 14)]) (p' := 0x1292c4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (4, 65), (13, 13), (14, 14)]) (p' := 0x1292c6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (4, 67), (14, 14)]) (p' := 0x1292c8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (4, 69)]) (p' := 0x1292ca) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (4, 71)]) (p' := 0x1292cc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 53)]) (p' := 0x1292cd) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1292ab [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1292ab :=
  Rest.liftedBlock (rest_l1292ab code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1292ab x hx)

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

theorem_by block_l129100_eval :
    program.runBlock (dialect code) ⟨.l129100, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129128_eval :
    program.runBlock (dialect code) ⟨.l129128, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129131_eval :
    program.runBlock (dialect code) ⟨.l129131, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12913b_eval :
    program.runBlock (dialect code) ⟨.l12913b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129144_eval :
    program.runBlock (dialect code) ⟨.l129144, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129154_eval :
    program.runBlock (dialect code) ⟨.l129154, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12915e_eval :
    program.runBlock (dialect code) ⟨.l12915e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129168_eval :
    program.runBlock (dialect code) ⟨.l129168, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129180_eval :
    program.runBlock (dialect code) ⟨.l129180, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129184_eval :
    program.runBlock (dialect code) ⟨.l129184, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129195_eval :
    program.runBlock (dialect code) ⟨.l129195, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12919d_eval :
    program.runBlock (dialect code) ⟨.l12919d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291a4_eval :
    program.runBlock (dialect code) ⟨.l1291a4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291a9_eval :
    program.runBlock (dialect code) ⟨.l1291a9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291b9_eval :
    program.runBlock (dialect code) ⟨.l1291b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291bf_eval :
    program.runBlock (dialect code) ⟨.l1291bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291ce_eval :
    program.runBlock (dialect code) ⟨.l1291ce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291d9_eval :
    program.runBlock (dialect code) ⟨.l1291d9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291db_eval :
    program.runBlock (dialect code) ⟨.l1291db, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291df_eval :
    program.runBlock (dialect code) ⟨.l1291df, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291e2_eval :
    program.runBlock (dialect code) ⟨.l1291e2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291ed_eval :
    program.runBlock (dialect code) ⟨.l1291ed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1291f5_eval :
    program.runBlock (dialect code) ⟨.l1291f5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129200_eval :
    program.runBlock (dialect code) ⟨.l129200, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129247_eval :
    program.runBlock (dialect code) ⟨.l129247, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12924c_eval :
    program.runBlock (dialect code) ⟨.l12924c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129260_eval :
    program.runBlock (dialect code) ⟨.l129260, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129275_eval :
    program.runBlock (dialect code) ⟨.l129275, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12927e_eval :
    program.runBlock (dialect code) ⟨.l12927e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1292ab_eval :
    program.runBlock (dialect code) ⟨.l1292ab, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
