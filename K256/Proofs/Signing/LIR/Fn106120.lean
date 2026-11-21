import K256.Proofs.Signing.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Signing.LIR.Generated.Values

namespace K256.Proofs.Signing.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR K256.Proofs.Verify.LIR

theorem rest_l106120 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106120 bytes_l106120) (entryMap (live .l106120))
      12 0x106120 bytes_l106120 b_l106120 := by
  have f0 : InstrSpec 0x106120 [0x55] (PushPre 0x106120 1) (pushR64Effect 0x106120 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106120 1 5).toInstrSpec (push_r64_effect_step 0x106120 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x106121 [0x41, 0x57] (PushPre 0x106121 2) (pushR64Effect 0x106121 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106121 2 15).toInstrSpec (push_r64_rex_effect_step 0x106121 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x106123 [0x41, 0x56] (PushPre 0x106123 2) (pushR64Effect 0x106123 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106123 2 14).toInstrSpec (push_r64_rex_effect_step 0x106123 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106125 [0x41, 0x55] (PushPre 0x106125 2) (pushR64Effect 0x106125 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106125 2 13).toInstrSpec (push_r64_rex_effect_step 0x106125 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x106127 [0x41, 0x54] (PushPre 0x106127 2) (pushR64Effect 0x106127 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106127 2 12).toInstrSpec (push_r64_rex_effect_step 0x106127 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x106129 [0x53] (PushPre 0x106129 1) (pushR64Effect 0x106129 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106129 1 3).toInstrSpec (push_r64_effect_step 0x106129 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10612a [0x48, 0x83, 0xEC, 0x38] (fun s => s.RIP = 0x10612a) (subR64Imm8Effect 0x10612a 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10612a 4 0x38).toInstrSpec (sub_r64_imm8_effect_step 0x10612a 0x48 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10612e [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x10612e) (movR64R64Effect 0x10612e 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10612e 14 6).toInstrSpec (mov_r64_r64_effect_step 0x10612e 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x106131 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x106131) (movR64R64Effect 0x106131 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x106131 3 7).toInstrSpec (mov_r64_r64_effect_step 0x106131 0x48 0xfb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x106134 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x106134) (movR64R64Effect 0x106134 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106134 7 4).toInstrSpec (mov_r64_r64_effect_step 0x106134 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x106137 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106137) (movR32Imm32Effect 0x106137 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x106137 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x106137 0xba (by decide) 0x1) pre_rip
  have f11 : InstrSpec 0x10613c [0xE8, 0x3F, 0x1A, 0x02, 0x00] (PushPre 0x10613c 5) (callEffect (fun _ => 0x127b80) 0x106141)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10613c 0x127b80 0x106141).toInstrSpec (call_rel32_effect_step 0x10613c 0x21a3f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106121) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106123) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106125) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106127) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106129) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10612a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10612e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106131) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106134) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(3, 69), (4, 65), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106137) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 73), (3, 69), (4, 65), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10613c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(2, 73), (3, 69), (4, 75), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l106120 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106120 :=
  Rest.liftedBlock (rest_l106120 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106120 x hx)

theorem rest_l106141 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106141 bytes_l106141) (entryMap (live .l106141))
      3 0x106141 bytes_l106141 b_l106141 := by
  have f0 : InstrSpec 0x106141 [0x8B, 0x04, 0x24] (LoadPre 0x106141 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x106141 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x106141 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106141 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x106141 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106144 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x106144) (cmpR32Imm8Effect 0x106144 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x106144 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x106144 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106144) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106147) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x106147 5 0xd5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106141 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106141 :=
  Rest.liftedBlock (rest_l106141 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106141 x hx)

theorem rest_l10614d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10614d bytes_l10614d) (entryMap (live .l10614d))
      3 0x10614d bytes_l10614d b_l10614d := by
  have f0 : InstrSpec 0x10614d [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x10614d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10614d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10614d 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10614d 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10614d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106152 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x106152) (cmpR64Imm8Effect 0x106152 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x106152 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x106152 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106152) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106156) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x106156 5 0x15b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10614d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10614d :=
  Rest.liftedBlock (rest_l10614d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10614d x hx)

theorem rest_l10615c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10615c bytes_l10615c) (entryMap (live .l10615c))
      4 0x10615c bytes_l10615c b_l10615c := by
  have f0 : InstrSpec 0x10615c [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10615c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10615c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10615c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10615c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10615c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106161 [0x0F, 0xBE, 0x28] (LoadPre 0x106161 (fun s => AddrMode.addr (.base 0 .none) s (0x106161 + BitVec.ofNat 64 3)) 1) (movsxR32M8Effect 0x106161 3 5 (.base 0 .none))
      [.gpr 0] [] [.reg 5, .rip] :=
    (movsxR32M8Effect_footprint 0x106161 3 5 (.base 0 .none)).toInstrSpec (movsx_r32_m8_effect_step 0x106161 5 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106164 [0x85, 0xED] (fun s => s.RIP = 0x106164) (testR32R32Effect 0x106164 2 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x106164 2 5 5).toInstrSpec (test_r32_r32_effect_step 0x106164 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106161) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106164) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106166) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x106166 8 0xe) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10615c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10615c :=
  Rest.liftedBlock (rest_l10615c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10615c x hx)

theorem rest_l106168 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106168 bytes_l106168) (entryMap (live .l106168))
      1 0x106168 bytes_l106168 b_l106168 := by
  have f0 : InstrSpec 0x106168 [0x89, 0x6B, 0x04] (StorePre 0x106168 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106168 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106168 5 (.base 3 (.d8 0x4)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106168 5 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x106168 5 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10616b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l106168 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106168 :=
  Rest.liftedBlock (rest_l106168 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106168 x hx)

theorem rest_l10616b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10616b bytes_l10616b) (entryMap (live .l10616b))
      2 0x10616b bytes_l10616b b_l10616b := by
  have f0 : InstrSpec 0x10616b [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x10616b 6 (fun s => AddrMode.addr (.base 3 .none) s (0x10616b + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x10616b 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x10616b 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x10616b (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106171) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel32_effect_step 0x106171 0xeb (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10616b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10616b :=
  Rest.liftedBlock (rest_l10616b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10616b x hx)

theorem rest_l106176 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106176 bytes_l106176) (entryMap (live .l106176))
      3 0x106176 bytes_l106176 b_l106176 := by
  have f0 : InstrSpec 0x106176 [0x89, 0xE8] (fun s => s.RIP = 0x106176) (movR32R32Effect 0x106176 2 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106176 2 0 5).toInstrSpec (mov_r32_r32_effect_step 0x106176 0xe8 (by decide)) pre_rip
  have f1 : InstrSpec 0x106178 [0xF6, 0xD8] (fun s => s.RIP = 0x106178) (negR8Effect 0x106178 2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR8Effect_footprint 0x106178 2 0).toInstrSpec (neg_r8_effect_step 0x106178 0xd8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106178) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10617a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x10617a 1 0x1b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106176 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106176 :=
  Rest.liftedBlock (rest_l106176 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106176 x hx)

theorem rest_l10617c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10617c bytes_l10617c) (entryMap (live .l10617c))
      6 0x10617c bytes_l10617c b_l10617c := by
  have f0 : InstrSpec 0x10617c [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x10617c 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x10617c + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x10617c (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x10617c (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x10617c 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x106181 [0x41, 0x8B, 0x46, 0x1C] (LoadPre 0x106181 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x106181 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x106181 0 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x106181 0 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x106181 0x41 (by decide) 0 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106185 [0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x106185 6 (fun s => AddrMode.addr (.base 3 .none) s (0x106185 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x106185 6 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x106185 6 (.base 3 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x106185 (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10618b [0x89, 0x43, 0x04] (StorePre 0x10618b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x10618b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10618b 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10618b 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x10618b 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10618e [0xC6, 0x43, 0x08, 0x04] (StorePre 0x10618e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10618e + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x10618e (.base 3 (.d8 0x8)) 0x4)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x10618e (.base 3 (.d8 0x8)) 0x4).toInstrSpec (mov_m8_imm8_effect_step 0x10618e (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x4) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106181) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106185) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10618b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10618e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106192) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x106192 0xca (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10617c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10617c :=
  Rest.liftedBlock (rest_l10617c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10617c x hx)

theorem rest_l106197 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106197 bytes_l106197) (entryMap (live .l106197))
      2 0x106197 bytes_l106197 b_l106197 := by
  have f0 : InstrSpec 0x106197 [0x40, 0x80, 0xFD, 0x85] (fun s => s.RIP = 0x106197) (cmpR8Imm8Effect 0x106197 4 5 0x85)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x106197 4 5 0x85).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x106197 0x40 0xfd 0x85 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10619b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10619b 3 0xfe) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106197 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106197 :=
  Rest.liftedBlock (rest_l106197 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106197 x hx)

theorem rest_l1061a1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1061a1 bytes_l1061a1) (entryMap (live .l1061a1))
      2 0x1061a1 bytes_l1061a1 b_l1061a1 := by
  have f0 : InstrSpec 0x1061a1 [0x40, 0xF6, 0xC5, 0x7F] (fun s => s.RIP = 0x1061a1) (testR8Imm8Effect 0x1061a1 5 0x7f)
      [.gpr 5] [] [.flags, .rip] :=
    (testR8Imm8Effect_footprint 0x1061a1 5 0x7f).toInstrSpec (test_r8_imm8_effect_step 0x1061a1 0x40 0xc5 0x7f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1061a5 4 0xc8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1061a1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1061a1 :=
  Rest.liftedBlock (rest_l1061a1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1061a1 x hx)

theorem rest_l1061ab [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1061ab bytes_l1061ab) (entryMap (live .l1061ab))
      5 0x1061ab bytes_l1061ab b_l1061ab := by
  have f0 : InstrSpec 0x1061ab [0x41, 0x89, 0xED] (fun s => s.RIP = 0x1061ab) (movR32R32Effect 0x1061ab 3 13 5)
      [.gpr 5] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x1061ab 3 13 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x1061ab 0x41 0xed (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1061ae [0x41, 0x83, 0xE5, 0x7F] (fun s => s.RIP = 0x1061ae) (andR32Imm8Effect 0x1061ae 4 13 0x7f)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1061ae 4 13 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x1061ae 0x41 0xe5 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1061b2 [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x1061b2) (xorR32R32Effect 0x1061b2 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1061b2 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x1061b2 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1061b5 [0x49, 0x89, 0xE7] (fun s => s.RIP = 0x1061b5) (movR64R64Effect 0x1061b5 15 4)
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1061b5 15 4).toInstrSpec (mov_r64_r64_effect_step 0x1061b5 0x49 0xe7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1061b8 [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1061b8) (fun _ => nopEffect 0x1061b8 8)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1061b8 8).toInstrSpec (nop_m_effect_step 0x1061b8 [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061ae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061b5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 55), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061b8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 55), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061c0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l1061ab [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1061ab :=
  Rest.liftedBlock (rest_l1061ab code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1061ab x hx)

theorem rest_l1061c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1061c0 bytes_l1061c0) (entryMap (live .l1061c0))
      4 0x1061c0 bytes_l1061c0 b_l1061c0 := by
  have f0 : InstrSpec 0x1061c0 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x1061c0) (movR64R64Effect 0x1061c0 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1061c0 7 15).toInstrSpec (mov_r64_r64_effect_step 0x1061c0 0x4c 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1061c3 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1061c3) (movR64R64Effect 0x1061c3 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1061c3 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1061c3 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1061c6 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1061c6) (movR32Imm32Effect 0x1061c6 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1061c6 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1061c6 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x1061cb [0xE8, 0xB0, 0x19, 0x02, 0x00] (PushPre 0x1061cb 5) (callEffect (fun _ => 0x127b80) 0x1061d0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1061cb 0x127b80 0x1061d0).toInstrSpec (call_rel32_effect_step 0x1061cb 0x219b0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061c6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061cb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1061c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1061c0 :=
  Rest.liftedBlock (rest_l1061c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1061c0 x hx)

theorem rest_l1061d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1061d0 bytes_l1061d0) (entryMap (live .l1061d0))
      3 0x1061d0 bytes_l1061d0 b_l1061d0 := by
  have f0 : InstrSpec 0x1061d0 [0x8B, 0x04, 0x24] (LoadPre 0x1061d0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1061d0 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1061d0 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1061d0 0 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x1061d0 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1061d3 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1061d3) (cmpR32Imm8Effect 0x1061d3 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1061d3 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1061d3 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061d6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1061d6 5 0x4a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1061d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1061d0 :=
  Rest.liftedBlock (rest_l1061d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1061d0 x hx)

theorem rest_l1061d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1061d8 bytes_l1061d8) (entryMap (live .l1061d8))
      3 0x1061d8 bytes_l1061d8 b_l1061d8 := by
  have f0 : InstrSpec 0x1061d8 [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x1061d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1061d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1061d8 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1061d8 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1061d8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1061dd [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x1061dd) (cmpR64Imm8Effect 0x1061dd 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1061dd 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x1061dd 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061e1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1061e1 5 0xd0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1061d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1061d8 :=
  Rest.liftedBlock (rest_l1061d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1061d8 x hx)

theorem rest_l1061e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1061e7 bytes_l1061e7) (entryMap (live .l1061e7))
      7 0x1061e7 bytes_l1061e7 b_l1061e7 := by
  have f0 : InstrSpec 0x1061e7 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1061e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1061e7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1061e7 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1061e7 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1061e7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1061ec [0x44, 0x89, 0xE2] (fun s => s.RIP = 0x1061ec) (movR32R32Effect 0x1061ec 3 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1061ec 3 2 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x1061ec 0x44 0xe2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1061ef [0x44, 0x0F, 0xB6, 0x20] (LoadPre 0x1061ef (fun s => AddrMode.addr (.base 0 .none) s (0x1061ef + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1061ef 4 12 (.base 0 .none))
      [.gpr 0] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x1061ef 4 12 (.base 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1061ef 0x44 (by decide) 4 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1061f3 [0xC1, 0xE2, 0x08] (fun s => s.RIP = 0x1061f3) (shlR32Effect 0x1061f3 3 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x1061f3 3 2 8).toInstrSpec (shl_r32_imm8_effect_step 0x1061f3 0xe2 0x8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1061f6 [0x41, 0x09, 0xD4] (fun s => s.RIP = 0x1061f6) (orR32R32Effect 0x1061f6 3 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1061f6 3 12 2).toInstrSpec (or_r32_r32_rex_effect_step 0x1061f6 0x41 0xd4 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1061f9 [0x49, 0xFF, 0xCD] (fun s => s.RIP = 0x1061f9) (decR64Effect 0x1061f9 13)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (decR64Effect_footprint 0x1061f9 13).toInstrSpec (dec_r64_effect_step 0x1061f9 0x49 0xcd (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061ec) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061ef) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061f3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061f6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061f9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 64) f5 .ZF (fun _ => rfl) (decR64Effect_fresh 0x1061f9 13 _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 63), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1061fc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x1061fc 5 0xc2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1061e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1061e7 :=
  Rest.liftedBlock (rest_l1061e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1061e7 x hx)

theorem rest_l1061fe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1061fe bytes_l1061fe) (entryMap (live .l1061fe))
      6 0x1061fe bytes_l1061fe b_l1061fe := by
  have f0 : InstrSpec 0x1061fe [0x44, 0x89, 0xE6] (fun s => s.RIP = 0x1061fe) (movR32R32Effect 0x1061fe 3 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x1061fe 3 6 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x1061fe 0x44 0xe6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106201 [0x83, 0xE6, 0x80] (fun s => s.RIP = 0x106201) (andR32Imm8Effect 0x106201 3 6 0x80)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x106201 3 6 0x80).toInstrSpec (and_r32_imm8_effect_step 0x106201 0xe6 0x80 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106204 [0xB0, 0x01] (fun s => s.RIP = 0x106204) (movR8Imm8Effect 0x106204 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x106204 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x106204 0xb0 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x106206 [0xB1, 0x81] (fun s => s.RIP = 0x106206) (movR8Imm8Effect 0x106206 2 1 0x81)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x106206 2 1 0x81).toInstrSpec (mov_r8_imm8_effect_step 0x106206 0xb1 (by decide) 0x81) pre_rip
  have f4 : InstrSpec 0x106208 [0x81, 0xFE, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106208) (cmpR32Imm32Effect 0x106208 6 6 0x80)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm32Effect_footprint 0x106208 6 6 0x80).toInstrSpec (cmp_r32_imm32_effect_step 0x106208 0xfe 0x80 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106201) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106204) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106206) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106208) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10620e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x10620e 4 0x7d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1061fe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1061fe :=
  Rest.liftedBlock (rest_l1061fe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1061fe x hx)

theorem rest_l106210 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106210 bytes_l106210) (entryMap (live .l106210))
      4 0x106210 bytes_l106210 b_l106210 := by
  have f0 : InstrSpec 0x106210 [0x81, 0xC2, 0x00, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x106210) (addR32Imm32Effect 0x106210 6 2 0xffffff00)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR32Imm32Effect_footprint 0x106210 6 2 0xffffff00).toInstrSpec (add_r32_imm32_effect_step 0x106210 0xc2 0xffffff00 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106216 [0xB1, 0x82] (fun s => s.RIP = 0x106216) (movR8Imm8Effect 0x106216 2 1 0x82)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x106216 2 1 0x82).toInstrSpec (mov_r8_imm8_effect_step 0x106216 0xb1 (by decide) 0x82) pre_rip
  have f2 : InstrSpec 0x106218 [0x81, 0xFA, 0x00, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x106218) (cmpR32Imm32Effect 0x106218 6 2 0xff00)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm32Effect_footprint 0x106218 6 2 0xff00).toInstrSpec (cmp_r32_imm32_effect_step 0x106218 0xfa 0xff00 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106216) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106218) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10621e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x10621e 3 0x56) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106210 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106210 :=
  Rest.liftedBlock (rest_l106210 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106210 x hx)

theorem rest_l106220 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106220 bytes_l106220) (entryMap (live .l106220))
      1 0x106220 bytes_l106220 b_l106220 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x106220 0x6b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106220 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106220 :=
  Rest.liftedBlock (rest_l106220 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106220 x hx)

theorem rest_l106222 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106222 bytes_l106222) (entryMap (live .l106222))
      15 0x106222 bytes_l106222 b_l106222 := by
  have f0 : InstrSpec 0x106222 [0x8B, 0x4C, 0x24, 0x04] (LoadPre 0x106222 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x106222 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106222 1 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x106222 1 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x106222 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106226 [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x106226 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106226 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106226 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x106226 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x106226 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10622b [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x10622b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10622b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10622b 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10622b 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10622b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106230 [0x48, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x106230 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106230 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106230 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106230 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x106230 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x106235 [0x48, 0x89, 0x7B, 0x30] (StorePre 0x106235 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x106235 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106235 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106235 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x106235 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x106239 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x106239 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106239 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106239 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106239 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x106239 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10623e [0x48, 0x89, 0x7B, 0x28] (StorePre 0x10623e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10623e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10623e 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10623e 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10623e 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x106242 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x106242 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106242 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106242 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x106242 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x106242 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x106247 [0x48, 0x89, 0x7B, 0x20] (StorePre 0x106247 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x106247 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106247 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106247 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x106247 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10624b [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x10624b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10624b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10624b 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10624b 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10624b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x106250 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x106250 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x106250 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106250 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106250 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x106250 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x106254 [0x89, 0x03] (StorePre 0x106254 2 (fun s => AddrMode.addr (.base 3 .none) s (0x106254 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x106254 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106254 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x106254 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x106256 [0x89, 0x4B, 0x04] (StorePre 0x106256 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106256 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x106256 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106256 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x106256 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x106259 [0x48, 0x89, 0x53, 0x08] (StorePre 0x106259 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x106259 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106259 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x106259 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x106259 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10625d [0x48, 0x89, 0x73, 0x10] (StorePre 0x10625d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10625d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10625d 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10625d 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10625d 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106226) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10622b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106230) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106235) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106239) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10623e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106242) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106247) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10624b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106250) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106254) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106256) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106259) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10625d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106261) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 75) (by decide) rfl

theorem block_l106222 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106222 :=
  Rest.liftedBlock (rest_l106222 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106222 x hx)

theorem rest_l106261 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106261 bytes_l106261) (entryMap (live .l106261))
      9 0x106261 bytes_l106261 b_l106261 := by
  have f0 : InstrSpec 0x106261 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x106261) (movR64R64Effect 0x106261 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x106261 0 3).toInstrSpec (mov_r64_r64_effect_step 0x106261 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106264 [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x106264) (addR64Imm8Effect 0x106264 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x106264 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x106264 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106268 [0x5B] (PopPre 0x106268) (popR64Effect 0x106268 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106268 1 3).toInstrSpec (pop_r64_effect_step 0x106268 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106269 [0x41, 0x5C] (PopPre 0x106269) (popR64Effect 0x106269 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106269 2 12).toInstrSpec (pop_r64_rex_effect_step 0x106269 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10626b [0x41, 0x5D] (PopPre 0x10626b) (popR64Effect 0x10626b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10626b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10626b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10626d [0x41, 0x5E] (PopPre 0x10626d) (popR64Effect 0x10626d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10626d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10626d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10626f [0x41, 0x5F] (PopPre 0x10626f) (popR64Effect 0x10626f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10626f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10626f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x106271 [0x5D] (PopPre 0x106271) (popR64Effect 0x106271 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106271 1 5).toInstrSpec (pop_r64_effect_step 0x106271 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x106272 [0xC3] (RetPre 0x106272) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x106272).toInstrSpec (ret_effect_step 0x106272) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106264) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106268) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106269) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10626b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10626d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10626f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106271) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106272) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l106261 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106261 :=
  Rest.liftedBlock (rest_l106261 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106261 x hx)

theorem rest_l106273 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106273 bytes_l106273) (entryMap (live .l106273))
      1 0x106273 bytes_l106273 b_l106273 := by
  have f0 : InstrSpec 0x106273 [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x106273) (xorR32R32Effect 0x106273 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106273 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x106273 0x45 0xe4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106276) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l106273 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106273 :=
  Rest.liftedBlock (rest_l106273 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106273 x hx)

theorem rest_l106276 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106276 bytes_l106276) (entryMap (live .l106276))
      6 0x106276 bytes_l106276 b_l106276 := by
  have f0 : InstrSpec 0x106276 [0x44, 0x89, 0xE1] (fun s => s.RIP = 0x106276) (movR32R32Effect 0x106276 3 1 12)
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106276 3 1 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x106276 0x44 0xe1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106279 [0x81, 0xE9, 0x00, 0x00, 0x01, 0x00] (fun s => s.RIP = 0x106279) (subR32Imm32Effect 0x106279 6 1 0x10000)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (subR32Imm32Effect_footprint 0x106279 6 1 0x10000).toInstrSpec (sub_r32_imm32_effect_step 0x106279 0xe9 0x10000 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10627f [0x0F, 0x93, 0xC0] (fun s => s.RIP = 0x10627f) (atFlags (condHolds 3) (setccR8Effect 0x10627f 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x10627f 3 0 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x10627f 3 0xc0 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x106282 [0x81, 0xF9, 0x00, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x106282) (cmpR32Imm32Effect 0x106282 6 1 0xff0000)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm32Effect_footprint 0x106282 6 1 0xff0000).toInstrSpec (cmp_r32_imm32_effect_step 0x106282 0xf9 0xff0000 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106288 [0xB1, 0x84] (fun s => s.RIP = 0x106288) (movR8Imm8Effect 0x106288 2 1 0x84)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x106288 2 1 0x84).toInstrSpec (mov_r8_imm8_effect_step 0x106288 0xb1 (by decide) 0x84) pre_rip
  have f5 : InstrSpec 0x10628a [0x80, 0xD9, 0x00] (fun s => s.RIP = 0x10628a) (atFlags StatusFlags.CF (sbbR8Imm8Effect 0x10628a 3 1 0x0))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (sbbR8Imm8Effect_footprint 0x10628a 3 1 0x0).toInstrSpec (StepEffect.atFlags fun c => (sbb_r8_imm8_effect_step 0x10628a 0xd9 0x0 c (by decide) (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106279) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10627f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106282) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106288) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 62), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10628a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 58), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10628d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l106276 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106276 :=
  Rest.liftedBlock (rest_l106276 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106276 x hx)

theorem rest_l10628d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10628d bytes_l10628d) (entryMap (live .l10628d))
      2 0x10628d bytes_l10628d b_l10628d := by
  have f0 : InstrSpec 0x10628d [0x84, 0xC0] (fun s => s.RIP = 0x10628d) (testR8R8Effect 0x10628d 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10628d 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x10628d 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10628f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x10628f 4 0xe) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10628d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10628d :=
  Rest.liftedBlock (rest_l10628d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10628d x hx)

theorem rest_l106291 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106291 bytes_l106291) (entryMap (live .l106291))
      2 0x106291 bytes_l106291 b_l106291 := by
  have f0 : InstrSpec 0x106291 [0x40, 0x38, 0xE9] (fun s => s.RIP = 0x106291) (cmpR8R8Effect 0x106291 3 1 5)
      [.gpr 1, .gpr 5] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x106291 3 1 5).toInstrSpec (cmp_r8_r8_rex_effect_step 0x106291 0x40 0xe9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106294) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x106294 5 0x9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106291 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106291 :=
  Rest.liftedBlock (rest_l106291 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106291 x hx)

theorem rest_l106296 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106296 bytes_l106296) (entryMap (live .l106296))
      2 0x106296 bytes_l106296 b_l106296 := by
  have f0 : InstrSpec 0x106296 [0x44, 0x89, 0x63, 0x04] (StorePre 0x106296 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x106296 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x106296 12 (.base 3 (.d8 0x4)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x106296 12 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x106296 0x44 (by decide) 4 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10629a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel32_effect_step 0x10629a 0xfffffecc (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l106296 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106296 :=
  Rest.liftedBlock (rest_l106296 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106296 x hx)

theorem rest_l10629f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10629f bytes_l10629f) (entryMap (live .l10629f))
      6 0x10629f bytes_l10629f b_l10629f := by
  have f0 : InstrSpec 0x10629f [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x10629f 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x10629f + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x10629f (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x10629f (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x10629f 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1062a4 [0x41, 0x8B, 0x46, 0x1C] (LoadPre 0x1062a4 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1062a4 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1062a4 0 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x1062a4 0 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1062a4 0x41 (by decide) 0 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1062a8 [0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1062a8 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1062a8 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1062a8 6 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1062a8 6 (.base 3 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x1062a8 (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1062ae [0x89, 0x43, 0x04] (StorePre 0x1062ae 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1062ae + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1062ae 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1062ae 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1062ae 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1062b1 [0xC6, 0x43, 0x08, 0x0D] (StorePre 0x1062b1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1062b1 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1062b1 (.base 3 (.d8 0x8)) 0xd)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1062b1 (.base 3 (.d8 0x8)) 0xd).toInstrSpec (mov_m8_imm8_effect_step 0x1062b1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0xd) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062a8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062ae) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062b1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062b5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x1062b5 0xaa (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10629f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10629f :=
  Rest.liftedBlock (rest_l10629f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10629f x hx)

theorem rest_l1062b7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1062b7 bytes_l1062b7) (entryMap (live .l1062b7))
      3 0x1062b7 bytes_l1062b7 b_l1062b7 := by
  have f0 : InstrSpec 0x1062b7 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1062b7) (movR32Imm32Effect 0x1062b7 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x1062b7 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1062b7 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x1062bc [0x48, 0xC7, 0xC2, 0x30, 0x25, 0x20, 0x00] (fun s => s.RIP = 0x1062bc) (movR64Imm32Effect 0x1062bc 2 0x202530)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x1062bc 2 0x202530).toInstrSpec (mov_r64_imm32_effect_step 0x1062bc 0x48 0xc2 (by decide) (by decide) (by decide) 0x202530) pre_rip
  have f2 : InstrSpec 0x1062c3 [0xE8, 0xC8, 0x39, 0x02, 0x00] (PushPre 0x1062c3 5) (callEffect (fun _ => 0x129c90) 0x1062c8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1062c3 0x129c90 0x1062c8).toInstrSpec (call_rel32_effect_step 0x1062c3 0x239c8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x1062bc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x1062c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1062b7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1062b7 :=
  Rest.liftedBlock (rest_l1062b7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1062b7 x hx)

theorem rest_l1062c8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1062c8 bytes_l1062c8) (entryMap (live .l1062c8))
      8 0x1062c8 bytes_l1062c8 b_l1062c8 := by
  have f0 : InstrSpec 0x1062c8 [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1062c8) (fun _ => nopEffect 0x1062c8 8)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1062c8 8).toInstrSpec (nop_m_effect_step 0x1062c8 [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1062d0 [0x41, 0x56] (PushPre 0x1062d0 2) (pushR64Effect 0x1062d0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1062d0 2 14).toInstrSpec (push_r64_rex_effect_step 0x1062d0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1062d2 [0x53] (PushPre 0x1062d2 1) (pushR64Effect 0x1062d2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1062d2 1 3).toInstrSpec (push_r64_effect_step 0x1062d2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1062d3 [0x48, 0x81, 0xEC, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1062d3) (subR64Imm32Effect 0x1062d3 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1062d3 4 0x88).toInstrSpec (sub_r64_imm32_effect_step 0x1062d3 0x48 0xec 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1062da [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x1062da) (movR64R64Effect 0x1062da 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1062da 6 7).toInstrSpec (mov_r64_r64_effect_step 0x1062da 0x48 0xfe (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1062dd [0x48, 0x8D, 0x7C, 0x24, 0x0F] (fun s => s.RIP = 0x1062dd) (leaR64Effect 0x1062dd 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1062dd 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x1062dd 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1062e2 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1062e2) (movR32Imm32Effect 0x1062e2 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1062e2 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1062e2 0xba (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x1062e7 [0xE8, 0xF4, 0xB2, 0x01, 0x00] (PushPre 0x1062e7 5) (callEffect (fun _ => 0x1215e0) 0x1062ec)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1062e7 0x1215e0 0x1062ec).toInstrSpec (call_rel32_effect_step 0x1062e7 0x1b2f4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062d0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 54), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062d2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 56), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062d3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 58), (5, 5), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062da) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 58), (5, 5), (6, 60), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062dd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(3, 3), (4, 58), (5, 5), (6, 60), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062e2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 64), (3, 3), (4, 58), (5, 5), (6, 60), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062e7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 64), (3, 3), (4, 66), (5, 5), (6, 60), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e0) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l1062c8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1062c8 :=
  Rest.liftedBlock (rest_l1062c8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1062c8 x hx)

theorem rest_l1062ec [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1062ec bytes_l1062ec) (entryMap (live .l1062ec))
      7 0x1062ec bytes_l1062ec b_l1062ec := by
  have f0 : InstrSpec 0x1062ec [0x0F, 0xB6, 0x4C, 0x24, 0x0F] (LoadPre 0x1062ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1062ec + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1062ec 5 1 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1062ec 5 1 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x1062ec 1 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1062f1 [0x48, 0x83, 0xF9, 0x06] (fun s => s.RIP = 0x1062f1) (cmpR64Imm8Effect 0x1062f1 1 0x6)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1062f1 1 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x1062f1 0x48 0xf9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1062f5 [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x1062f5) (atFlags (condHolds 2) (setccR8Effect 0x1062f5 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1062f5 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1062f5 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1062f8 [0xB2, 0x3D] (fun s => s.RIP = 0x1062f8) (movR8Imm8Effect 0x1062f8 2 2 0x3d)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR8Imm8Effect_footprint 0x1062f8 2 2 0x3d).toInstrSpec (mov_r8_imm8_effect_step 0x1062f8 0xb2 (by decide) 0x3d) pre_rip
  have f4 : InstrSpec 0x1062fa [0xD2, 0xEA] (fun s => s.RIP = 0x1062fa) (shrR8ClEffect 0x1062fa 2 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR8ClEffect_footprint 0x1062fa 2 2).toInstrSpec (shr_r8_cl_effect_step 0x1062fa 0xea (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1062fc [0x84, 0xD0] (fun s => s.RIP = 0x1062fc) (testR8R8Effect 0x1062fc 2 0 2)
      [.gpr 0, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1062fc 2 0 2).toInstrSpec (test_r8_r8_effect_step 0x1062fc 0xd0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062f5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062f8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 53), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062fa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 53), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062fc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 53), (2, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1062fe) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x1062fe 5 0x2c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1062ec [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1062ec :=
  Rest.liftedBlock (rest_l1062ec code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1062ec x hx)

theorem rest_l106300 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106300 bytes_l106300) (entryMap (live .l106300))
      7 0x106300 bytes_l106300 b_l106300 := by
  have f0 : InstrSpec 0x106300 [0xC7, 0x44, 0x24, 0x50, 0x03, 0x00, 0x00, 0x00] (StorePre 0x106300 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x106300 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x106300 8 (.sib 4 none 0 (.d8 0x50)) 0x3)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x106300 8 (.sib 4 none 0 (.d8 0x50)) 0x3).toInstrSpec (mov_m32_imm32_effect_step 0x106300 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x106308 [0x48, 0x8D, 0x54, 0x24, 0x50] (fun s => s.RIP = 0x106308) (leaR64Effect 0x106308 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x106308 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x106308 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10630d [0xBE, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10630d) (movR32Imm32Effect 0x10630d 5 6 0xb)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10630d 5 6 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x10630d 0xbe (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x106312 [0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x106312) (movR64Imm32Effect 0x106312 7 0x202800)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x106312 7 0x202800).toInstrSpec (mov_r64_imm32_effect_step 0x106312 0x48 0xc7 (by decide) (by decide) (by decide) 0x202800) pre_rip
  have f4 : InstrSpec 0x106319 [0x48, 0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00] (fun s => s.RIP = 0x106319) (movR64Imm32Effect 0x106319 1 0x2027e0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x106319 1 0x2027e0).toInstrSpec (mov_r64_imm32_effect_step 0x106319 0x48 0xc1 (by decide) (by decide) (by decide) 0x2027e0) pre_rip
  have f5 : InstrSpec 0x106320 [0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x106320) (movR64Imm32Effect 0x106320 8 0x202810)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x106320 8 0x202810).toInstrSpec (mov_r64_imm32_effect_step 0x106320 0x49 0xc0 (by decide) (by decide) (by decide) 0x202810) pre_rip
  have f6 : InstrSpec 0x106327 [0xE8, 0x74, 0x32, 0x02, 0x00] (PushPre 0x106327 5) (callEffect (fun _ => 0x1295a0) 0x10632c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106327 0x1295a0 0x10632c).toInstrSpec (call_rel32_effect_step 0x106327 0x23274 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x106308) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (4, 4), (5, 5)]) (p' := 0x10630d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56)]) (p' := 0x106312) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x106319) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x106320) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x106327) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x1295a0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l106300 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106300 :=
  Rest.liftedBlock (rest_l106300 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106300 x hx)

theorem rest_l10632c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10632c bytes_l10632c) (entryMap (live .l10632c))
      2 0x10632c bytes_l10632c b_l10632c := by
  have f0 : InstrSpec 0x10632c [0x48, 0x8B, 0x1C, 0xCD, 0x48, 0x25, 0x20, 0x00] (LoadPre 0x10632c (fun s => AddrMode.addr (.abs (some 1) 3 0x202548) s (0x10632c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10632c 3 (.abs (some 1) 3 0x202548))
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10632c 3 (.abs (some 1) 3 0x202548)).toInstrSpec (mov_r64_m64_effect_step 0x10632c 0x48 (by decide) 3 (.abs (some 1) 3 0x202548) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106334 [0xE8, 0x97, 0x21, 0x00, 0x00] (PushPre 0x106334 5) (callEffect (fun _ => 0x1084d0) 0x106339)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106334 0x1084d0 0x106339).toInstrSpec (call_rel32_effect_step 0x106334 0x2197 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106334) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084d0) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l10632c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10632c :=
  Rest.liftedBlock (rest_l10632c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10632c x hx)

theorem rest_l106339 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106339 bytes_l106339) (entryMap (live .l106339))
      4 0x106339 bytes_l106339 b_l106339 := by
  have f0 : InstrSpec 0x106339 [0x4C, 0x8B, 0x35, 0xC0, 0x9C, 0x1F, 0x00] (LoadPre 0x106339 (fun s => AddrMode.addr (.rip 0x1f9cc0) s (0x106339 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x106339 14 (.rip 0x1f9cc0))
      [] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x106339 14 (.rip 0x1f9cc0)).toInstrSpec (mov_r64_m64_effect_step 0x106339 0x4c (by decide) 6 (.rip 0x1f9cc0) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106340 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x106340) (movR64R64Effect 0x106340 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x106340 0 14).toInstrSpec (mov_r64_r64_effect_step 0x106340 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106343 [0x48, 0x01, 0xD8] (fun s => s.RIP = 0x106343) (addR64R64Effect 0x106343 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x106343 0 3).toInstrSpec (add_r64_r64_effect_step 0x106343 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106340) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106343) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106346) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x106346 2 0x9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106339 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106339 :=
  Rest.liftedBlock (rest_l106339 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106339 x hx)

theorem rest_l106348 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106348 bytes_l106348) (entryMap (live .l106348))
      2 0x106348 bytes_l106348 b_l106348 := by
  have f0 : InstrSpec 0x106348 [0x48, 0x3B, 0x05, 0xB9, 0x9C, 0x1F, 0x00] (LoadPre 0x106348 (fun s => AddrMode.addr (.rip 0x1f9cb9) s (0x106348 + BitVec.ofNat 64 7)) 8) (cmpR64M64Effect 0x106348 0 (.rip 0x1f9cb9))
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64M64Effect_footprint 0x106348 0 (.rip 0x1f9cb9)).toInstrSpec (cmp_r64_m64_effect_step 0x106348 0x48 (by decide) 0 (.rip 0x1f9cb9) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10634f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x10634f 6 0xd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l106348 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106348 :=
  Rest.liftedBlock (rest_l106348 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106348 x hx)

theorem rest_l106351 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106351 bytes_l106351) (entryMap (live .l106351))
      3 0x106351 bytes_l106351 b_l106351 := by
  have f0 : InstrSpec 0x106351 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106351) (movR32Imm32Effect 0x106351 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x106351 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x106351 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x106356 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x106356) (movR64R64Effect 0x106356 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x106356 6 3).toInstrSpec (mov_r64_r64_effect_step 0x106356 0x48 0xde (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106359 [0xE8, 0x9E, 0x23, 0x02, 0x00] (PushPre 0x106359 5) (callEffect (fun _ => 0x1286fc) 0x10635e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106359 0x1286fc 0x10635e).toInstrSpec (call_rel32_effect_step 0x106359 0x2239e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 53)]) (p' := 0x106356) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x106359) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 55), (7, 53)]) (p' := 0x1286fc) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l106351 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106351 :=
  Rest.liftedBlock (rest_l106351 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106351 x hx)

theorem rest_l10635e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10635e bytes_l10635e) (entryMap (live .l10635e))
      3 0x10635e bytes_l10635e b_l10635e := by
  have f0 : InstrSpec 0x10635e [0x48, 0x89, 0x05, 0x9B, 0x9C, 0x1F, 0x00] (StorePre 0x10635e 7 (fun s => AddrMode.addr (.rip 0x1f9c9b) s (0x10635e + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x10635e 0 (.rip 0x1f9c9b))
      [.gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10635e 0 (.rip 0x1f9c9b)).toInstrSpec (mov_m64_r64_effect_step 0x10635e 0x48 (by decide) 0 (.rip 0x1f9c9b) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x106365 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x106365) (testR64R64Effect 0x106365 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x106365 14 14).toInstrSpec (test_r64_r64_effect_step 0x106365 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106365) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106368) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x106368 4 0xe7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10635e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10635e :=
  Rest.liftedBlock (rest_l10635e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10635e x hx)

theorem rest_l10636a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10636a bytes_l10636a) (entryMap (live .l10636a))
      4 0x10636a bytes_l10636a b_l10636a := by
  have f0 : InstrSpec 0x10636a [0x48, 0x8D, 0x74, 0x24, 0x0F] (fun s => s.RIP = 0x10636a) (leaR64Effect 0x10636a 6 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10636a 6 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x10636a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10636f [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10636f) (movR64R64Effect 0x10636f 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10636f 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10636f 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106372 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x106372) (movR64R64Effect 0x106372 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x106372 2 3).toInstrSpec (mov_r64_r64_effect_step 0x106372 0x48 0xda (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106375 [0xFF, 0x15, 0x55, 0xDA, 0x0F, 0x00] (GoesTo (CallMemPre 0x106375 (.rip 0xfda55)) (callEffect (callMemPtr 0x106375 (.rip 0xfda55)) (0x106375 + BitVec.ofNat 64 (callMemLen (.rip 0xfda55)))) 0x12a820) (callEffect (callMemPtr 0x106375 (.rip 0xfda55)) (0x106375 + BitVec.ofNat 64 (callMemLen (.rip 0xfda55))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x106375 (.rip 0xfda55)).toInstrSpec (call_m64_effect_step 0x106375 (.rip 0xfda55) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10636f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106372) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106375) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10636a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10636a :=
  Rest.liftedBlock (rest_l10636a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10636a x hx)

theorem rest_l10637b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10637b bytes_l10637b) (entryMap (live .l10637b))
      6 0x10637b bytes_l10637b b_l10637b := by
  have f0 : InstrSpec 0x10637b [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x10637b) (movR64R64Effect 0x10637b 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10637b 0 14).toInstrSpec (mov_r64_r64_effect_step 0x10637b 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10637e [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x10637e) (movR64R64Effect 0x10637e 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10637e 2 3).toInstrSpec (mov_r64_r64_effect_step 0x10637e 0x48 0xda (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106381 [0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106381) (addR64Imm32Effect 0x106381 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x106381 4 0x88).toInstrSpec (add_r64_imm32_effect_step 0x106381 0x48 0xc4 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106388 [0x5B] (PopPre 0x106388) (popR64Effect 0x106388 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106388 1 3).toInstrSpec (pop_r64_effect_step 0x106388 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x106389 [0x41, 0x5E] (PopPre 0x106389) (popR64Effect 0x106389 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x106389 2 14).toInstrSpec (pop_r64_rex_effect_step 0x106389 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10638b [0xC3] (RetPre 0x10638b) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10638b).toInstrSpec (ret_effect_step 0x10638b) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10637e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106381) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106388) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 59), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106389) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 59), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10638b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 67) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 59), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l10637b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10637b :=
  Rest.liftedBlock (rest_l10637b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10637b x hx)

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

theorem_by block_l106120_eval :
    program.runBlock (dialect code) ⟨.l106120, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106141_eval :
    program.runBlock (dialect code) ⟨.l106141, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10614d_eval :
    program.runBlock (dialect code) ⟨.l10614d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10615c_eval :
    program.runBlock (dialect code) ⟨.l10615c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106168_eval :
    program.runBlock (dialect code) ⟨.l106168, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10616b_eval :
    program.runBlock (dialect code) ⟨.l10616b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106176_eval :
    program.runBlock (dialect code) ⟨.l106176, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10617c_eval :
    program.runBlock (dialect code) ⟨.l10617c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106197_eval :
    program.runBlock (dialect code) ⟨.l106197, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1061a1_eval :
    program.runBlock (dialect code) ⟨.l1061a1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1061ab_eval :
    program.runBlock (dialect code) ⟨.l1061ab, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1061c0_eval :
    program.runBlock (dialect code) ⟨.l1061c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1061d0_eval :
    program.runBlock (dialect code) ⟨.l1061d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1061d8_eval :
    program.runBlock (dialect code) ⟨.l1061d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1061e7_eval :
    program.runBlock (dialect code) ⟨.l1061e7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1061fe_eval :
    program.runBlock (dialect code) ⟨.l1061fe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106210_eval :
    program.runBlock (dialect code) ⟨.l106210, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106220_eval :
    program.runBlock (dialect code) ⟨.l106220, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106222_eval :
    program.runBlock (dialect code) ⟨.l106222, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106261_eval :
    program.runBlock (dialect code) ⟨.l106261, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106273_eval :
    program.runBlock (dialect code) ⟨.l106273, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106276_eval :
    program.runBlock (dialect code) ⟨.l106276, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10628d_eval :
    program.runBlock (dialect code) ⟨.l10628d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106291_eval :
    program.runBlock (dialect code) ⟨.l106291, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106296_eval :
    program.runBlock (dialect code) ⟨.l106296, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10629f_eval :
    program.runBlock (dialect code) ⟨.l10629f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1062b7_eval :
    program.runBlock (dialect code) ⟨.l1062b7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1062c8_eval :
    program.runBlock (dialect code) ⟨.l1062c8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1062ec_eval :
    program.runBlock (dialect code) ⟨.l1062ec, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106300_eval :
    program.runBlock (dialect code) ⟨.l106300, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10632c_eval :
    program.runBlock (dialect code) ⟨.l10632c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106339_eval :
    program.runBlock (dialect code) ⟨.l106339, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106348_eval :
    program.runBlock (dialect code) ⟨.l106348, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106351_eval :
    program.runBlock (dialect code) ⟨.l106351, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10635e_eval :
    program.runBlock (dialect code) ⟨.l10635e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10636a_eval :
    program.runBlock (dialect code) ⟨.l10636a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10637b_eval :
    program.runBlock (dialect code) ⟨.l10637b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
