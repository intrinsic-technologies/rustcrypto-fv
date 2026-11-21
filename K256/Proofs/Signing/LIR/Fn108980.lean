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

theorem rest_l108980 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108980 bytes_l108980) (entryMap (live .l108980))
      11 0x108980 bytes_l108980 b_l108980 := by
  have f0 : InstrSpec 0x108980 [0x55] (PushPre 0x108980 1) (pushR64Effect 0x108980 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108980 1 5).toInstrSpec (push_r64_effect_step 0x108980 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x108981 [0x41, 0x57] (PushPre 0x108981 2) (pushR64Effect 0x108981 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108981 2 15).toInstrSpec (push_r64_rex_effect_step 0x108981 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x108983 [0x41, 0x56] (PushPre 0x108983 2) (pushR64Effect 0x108983 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108983 2 14).toInstrSpec (push_r64_rex_effect_step 0x108983 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x108985 [0x41, 0x55] (PushPre 0x108985 2) (pushR64Effect 0x108985 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108985 2 13).toInstrSpec (push_r64_rex_effect_step 0x108985 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x108987 [0x41, 0x54] (PushPre 0x108987 2) (pushR64Effect 0x108987 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108987 2 12).toInstrSpec (push_r64_rex_effect_step 0x108987 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x108989 [0x53] (PushPre 0x108989 1) (pushR64Effect 0x108989 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108989 1 3).toInstrSpec (push_r64_effect_step 0x108989 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10898a [0x48, 0x83, 0xEC, 0x78] (fun s => s.RIP = 0x10898a) (subR64Imm8Effect 0x10898a 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10898a 4 0x78).toInstrSpec (sub_r64_imm8_effect_step 0x10898a 0x48 0xec 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10898e [0x44, 0x89, 0xCD] (fun s => s.RIP = 0x10898e) (movR32R32Effect 0x10898e 3 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x10898e 3 5 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x10898e 0x44 0xcd (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x108991 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x108991) (movR64R64Effect 0x108991 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x108991 3 7).toInstrSpec (mov_r64_r64_effect_step 0x108991 0x48 0xfb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x108994 [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x108994) (leaR64Effect 0x108994 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x108994 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108994 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x108999 [0xE8, 0x42, 0xFB, 0xFF, 0xFF] (PushPre 0x108999 5) (callEffect (fun _ => 0x1084e0) 0x10899e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x108999 0x1084e0 0x10899e).toInstrSpec (call_rel32_effect_step 0x108999 0xfffffb42 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108981) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108983) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108985) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108987) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108989) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10898a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10898e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108991) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108994) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 71), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108999) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 73), (5, 67), (6, 6), (7, 71), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e0) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l108980 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108980 :=
  Rest.liftedBlock (rest_l108980 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108980 x hx)

theorem rest_l10899e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10899e bytes_l10899e) (entryMap (live .l10899e))
      5 0x10899e bytes_l10899e b_l10899e := by
  have f0 : InstrSpec 0x10899e [0xB9, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10899e) (movR32Imm32Effect 0x10899e 5 1 0x40)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10899e 5 1 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x10899e 0xb9 (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x1089a3 [0x89, 0x6C, 0x24, 0x44] (StorePre 0x1089a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1089a3 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1089a3 5 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1089a3 5 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_m32_r32_low_effect_step 0x1089a3 5 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1089a7 [0x29, 0xE9] (fun s => s.RIP = 0x1089a7) (subR32R32Effect 0x1089a7 2 1 5)
      [.gpr 1, .gpr 5] [] [.reg 1, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1089a7 2 1 5).toInstrSpec (sub_r32_r32_effect_step 0x1089a7 0xe9 (by decide)) pre_rip
  have f3 : InstrSpec 0x1089a9 [0x83, 0xF9, 0x40] (fun s => s.RIP = 0x1089a9) (cmpR32Imm8Effect 0x1089a9 3 1 0x40)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1089a9 3 1 0x40).toInstrSpec (cmp_r32_imm8_effect_step 0x1089a9 0xf9 0x40 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 56), (3, 3), (4, 4), (5, 5), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089a9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 56), (3, 3), (4, 4), (5, 5), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089ac) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x1089ac 3 0x447) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10899e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10899e :=
  Rest.liftedBlock (rest_l10899e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10899e x hx)

theorem rest_l1089b2_6 [Bindings] (code : CodeMap) :
    Rest (n := 286) code lifted (codeRange 0x1089b2 bytes_l1089b2) [(0, 247), (1, 1), (3, 260), (4, 4), (5, 270), (6, 282), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]
      12 0x108b73 bytes_l1089b2_6 b_l1089b2_6 := by
  have f120 : InstrSpec 0x108b73 [0x0F, 0xB6, 0x54, 0x24, 0x10] (LoadPre 0x108b73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b73 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108b73 5 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x108b73 5 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x108b73 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x108b78 [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x108b78 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b78 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b78 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x108b78 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x108b78 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f122 : InstrSpec 0x108b7d [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x10] (LoadPre 0x108b7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b7d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108b7d 6 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x108b7d 6 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108b7d 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f123 : InstrSpec 0x108b83 [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x108b83 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b83 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b83 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x108b83 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x108b83 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f124 : InstrSpec 0x108b88 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x10] (LoadPre 0x108b88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b88 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108b88 6 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x108b88 6 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108b88 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f125 : InstrSpec 0x108b8e [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x108b8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b8e + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b8e 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x108b8e 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x108b8e 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f126 : InstrSpec 0x108b93 [0x0F, 0xB6, 0x7C, 0x24, 0x10] (LoadPre 0x108b93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b93 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108b93 5 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x108b93 5 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x108b93 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f127 : InstrSpec 0x108b98 [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x108b98 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b98 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b98 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x108b98 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x108b98 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f128 : InstrSpec 0x108b9d [0x4C, 0x8D, 0x4C, 0x24, 0x10] (fun s => s.RIP = 0x108b9d) (leaR64Effect 0x108b9d 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x108b9d 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108b9d 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x108ba2 [0x41, 0x0F, 0x95, 0xC1] (fun s => s.RIP = 0x108ba2) (atFlags (condHolds 5) (setccR8Effect 0x108ba2 4 9))
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (setccR8Effect_footprint 0x108ba2 4 9 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x108ba2 5 0x41 (by decide) 0xc1 (by decide) c)) pre_rip
  have f130 : InstrSpec 0x108ba6 [0x83, 0x7C, 0x24, 0x44, 0x40] (LoadPre 0x108ba6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x108ba6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x108ba6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x40)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x108ba6 5 (.sib 4 none 0 (.d8 0x44)) 0x40).toInstrSpec (cmp_m32_imm8_effect_step 0x108ba6 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide) 0x40) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f120 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b78) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.exec (n := 288) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b7d) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f122 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 289), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b83) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.exec (n := 291) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 289), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b88) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f124 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b8e) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.exec (n := 294) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b93) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f126 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (7, 295), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b98) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.exec (n := 297) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (7, 295), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b9d) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f128 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (7, 295), (8, 265), (9, 298), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ba2) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f129 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (7, 295), (8, 265), (9, 300), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ba6) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f130 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (7, 295), (8, 265), (9, 300), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (16, 302), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bab) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 304) (jcc_rel32_effect_step 0x108bab 3 0x248) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l1089b2_5 [Bindings] (code : CodeMap) :
    Rest (n := 249) code lifted (codeRange 0x1089b2 bytes_l1089b2) [(0, 247), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 243), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]
      32 0x108b1f bytes_l1089b2_5 b_l1089b2_5 := by
  have f100 : InstrSpec 0x108b1f [0x49, 0x21, 0xC6] (fun s => s.RIP = 0x108b1f) (andR64R64Effect 0x108b1f 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108b1f 14 0).toInstrSpec (and_r64_r64_effect_step 0x108b1f 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x108b22 [0x49, 0x09, 0xFE] (fun s => s.RIP = 0x108b22) (orR64R64Effect 0x108b22 14 7)
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108b22 14 7).toInstrSpec (or_r64_r64_effect_step 0x108b22 0x49 0xfe (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x108b25 [0x49, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x108b25) (shrR64Effect 0x108b25 4 14 63)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64Effect_footprint 0x108b25 4 14 63).toInstrSpec (shr_r64_imm8_effect_step 0x108b25 0x49 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x108b29 [0x4C, 0x89, 0x74, 0x24, 0x10] (StorePre 0x108b29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108b29 14 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108b29 14 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108b29 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f104 : InstrSpec 0x108b2e [0x48, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x108b2e) (leaR64Effect 0x108b2e 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x108b2e 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108b2e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x108b33 [0x48, 0x89, 0x6C, 0x24, 0x48] (StorePre 0x108b33 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108b33 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108b33 5 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108b33 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x108b33 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f106 : InstrSpec 0x108b38 [0x48, 0x89, 0xEB] (fun s => s.RIP = 0x108b38) (movR64R64Effect 0x108b38 3 5)
      [.gpr 5] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x108b38 3 5).toInstrSpec (mov_r64_r64_effect_step 0x108b38 0x48 0xeb (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x108b3b [0x48, 0xF7, 0xDB] (fun s => s.RIP = 0x108b3b) (negR64Effect 0x108b3b 3)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (negR64Effect_footprint 0x108b3b 3).toInstrSpec (neg_r64_effect_step 0x108b3b 0x48 0xdb (by decide) (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x108b3e [0x41, 0xB8, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108b3e) (movR32Imm32Effect 0x108b3e 6 8 0x0)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x108b3e 6 8 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x108b3e 0x41 0xb8 (by decide) (by decide) 0x0) pre_rip
  have f109 : InstrSpec 0x108b44 [0x4D, 0x19, 0xE0] (fun s => s.RIP = 0x108b44) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b44 8 12))
      [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x108b44 8 12).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x108b44 0x4d 0xe0 c (by decide) (by decide))) pre_rip
  have f110 : InstrSpec 0x108b47 [0xBD, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108b47) (movR32Imm32Effect 0x108b47 5 5 0x0)
      [] [] [.reg 5, .rip] :=
    (movR32Imm32Effect_footprint 0x108b47 5 5 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x108b47 0xbd (by decide) 0x0) pre_rip
  have f111 : InstrSpec 0x108b4c [0x4C, 0x19, 0xDD] (fun s => s.RIP = 0x108b4c) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4c 5 11))
      [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 5, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x108b4c 5 11).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x108b4c 0x4c 0xdd c (by decide) (by decide))) pre_rip
  have f112 : InstrSpec 0x108b4f [0x4D, 0x19, 0xEA] (fun s => s.RIP = 0x108b4f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4f 10 13))
      [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (sbbR64R64Effect_footprint 0x108b4f 10 13).toInstrSpec (StepEffect.atFlags fun c => (sbb_r64_r64_effect_step 0x108b4f 0x4d 0xea c (by decide) (by decide))) pre_rip
  have f113 : InstrSpec 0x108b52 [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x108b52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108b52 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x108b52 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x108b52 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f114 : InstrSpec 0x108b57 [0x0F, 0x93, 0x44, 0x24, 0x10] (StorePre 0x108b57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b57 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 3) (setccM8Effect 0x108b57 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF] [.rip] :=
    (setccM8Effect_footprint 0x108b57 5 (.sib 4 none 0 (.d8 0x10)) 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x108b57 3 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f115 : InstrSpec 0x108b5c [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x108b5c) (testR64R64Effect 0x108b5c 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x108b5c 2 2).toInstrSpec (test_r64_r64_effect_step 0x108b5c 0x48 0xd2 (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x108b5f [0x48, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x108b5f) (leaR64Effect 0x108b5f 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x108b5f 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108b5f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x108b64 [0x0F, 0xB6, 0x74, 0x24, 0x10] (LoadPre 0x108b64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b64 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108b64 5 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x108b64 5 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x108b64 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f118 : InstrSpec 0x108b69 [0x0F, 0x95, 0x44, 0x24, 0x10] (StorePre 0x108b69 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b69 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b69 5 (.sib 4 none 0 (.d8 0x10))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x108b69 5 (.sib 4 none 0 (.d8 0x10)) 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x108b69 5 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f119 : InstrSpec 0x108b6e [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x108b6e) (leaR64Effect 0x108b6e 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x108b6e 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108b6e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f100 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 247), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 249), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b22) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f101 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 247), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 251), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b25) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f102 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 247), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b29) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.exec (n := 255) (ρ' := [(0, 247), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b2e) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 256) (RestInside.exec (n := 256) (ρ' := [(0, 247), (1, 1), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b33) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 257) (RestInside.exec (n := 257) (ρ' := [(0, 247), (1, 1), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b38) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 258) (RestInside.out (n := 258) f106 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 259) (ρ' := [(0, 247), (1, 1), (3, 258), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b3b) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 260) (RestInside.out (n := 260) f107 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 261) f107 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 262) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (16, 261), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b3e) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f108 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 123), (6, 235), (7, 241), (8, 263), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (16, 261), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b44) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f109 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 266) f109 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x108b44 8 12 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 267) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 123), (6, 235), (7, 241), (8, 265), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (16, 266), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b47) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f110 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 268), (6, 235), (7, 241), (8, 265), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (16, 266), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b4c) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f111 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 271) f111 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x108b4c 5 11 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 272) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 270), (6, 235), (7, 241), (8, 265), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (16, 271), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b4f) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f112 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 274) f112 .CF (fun _ => rfl) (sbbR64R64Effect_fresh 0x108b4f 10 13 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 275) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 270), (6, 235), (7, 241), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (16, 274), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b52) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f113 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 247), (1, 1), (2, 276), (3, 260), (4, 4), (5, 270), (6, 235), (7, 241), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (16, 274), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b57) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.exec (n := 278) (ρ' := [(0, 247), (1, 1), (2, 276), (3, 260), (4, 4), (5, 270), (6, 235), (7, 241), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (16, 274), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b5c) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f115 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 247), (1, 1), (2, 276), (3, 260), (4, 4), (5, 270), (6, 235), (7, 241), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b5f) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.exec (n := 281) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 270), (6, 235), (7, 241), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b64) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f117 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 270), (6, 282), (7, 241), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b69) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.exec (n := 284) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 270), (6, 282), (7, 241), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b6e) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 285) (RestInside.exec (n := 285) (ρ' := [(0, 247), (1, 1), (3, 260), (4, 4), (5, 270), (6, 282), (8, 265), (9, 139), (10, 273), (11, 183), (12, 156), (13, 210), (14, 253), (15, 162), (19, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b73) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1089b2_6 code

theorem rest_l1089b2_4 [Bindings] (code : CodeMap) :
    Rest (n := 210) code lifted (codeRange 0x1089b2 bytes_l1089b2) [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 111), (8, 206), (9, 139), (10, 113), (11, 183), (12, 156), (13, 208), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]
      52 0x108ade bytes_l1089b2_4 b_l1089b2_4 := by
  have f80 : InstrSpec 0x108ade [0x4D, 0x01, 0xC5] (fun s => s.RIP = 0x108ade) (addR64R64Effect 0x108ade 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108ade 13 8).toInstrSpec (add_r64_r64_effect_step 0x108ade 0x4d 0xc5 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x108ae1 [0x48, 0xF7, 0xD7] (fun s => s.RIP = 0x108ae1) (notR64Effect 0x108ae1 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (notR64Effect_footprint 0x108ae1 7).toInstrSpec (not_r64_effect_step 0x108ae1 0x48 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x108ae4 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x108ae4) (movR64R64Effect 0x108ae4 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108ae4 8 0).toInstrSpec (mov_r64_r64_effect_step 0x108ae4 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x108ae7 [0x49, 0x21, 0xF8] (fun s => s.RIP = 0x108ae7) (andR64R64Effect 0x108ae7 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108ae7 8 7).toInstrSpec (and_r64_r64_effect_step 0x108ae7 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x108aea [0x48, 0x09, 0xC7] (fun s => s.RIP = 0x108aea) (orR64R64Effect 0x108aea 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108aea 7 0).toInstrSpec (or_r64_r64_effect_step 0x108aea 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x108aed [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x108aed) (xorR32R32Effect 0x108aed 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108aed 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x108aed 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x108af0 [0x4C, 0x21, 0xEF] (fun s => s.RIP = 0x108af0) (andR64R64Effect 0x108af0 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108af0 7 13).toInstrSpec (and_r64_r64_effect_step 0x108af0 0x4c 0xef (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x108af3 [0x4C, 0x09, 0xC7] (fun s => s.RIP = 0x108af3) (orR64R64Effect 0x108af3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108af3 7 8).toInstrSpec (or_r64_r64_effect_step 0x108af3 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x108af6 [0x48, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x108af6) (shrR64Effect 0x108af6 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x108af6 4 7 63).toInstrSpec (shr_r64_imm8_effect_step 0x108af6 0x48 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x108afa [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x108afa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108afa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108afa 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108afa 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108afa 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f90 : InstrSpec 0x108aff [0x31, 0xC0] (fun s => s.RIP = 0x108aff) (xorR32R32Effect 0x108aff 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108aff 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x108aff 0xc0 (by decide)) pre_rip
  have f91 : InstrSpec 0x108b01 [0x48, 0x2B, 0x44, 0x24, 0x10] (LoadPre 0x108b01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b01 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108b01 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108b01 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x108b01 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f92 : InstrSpec 0x108b06 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x108b06) (movR64R64Effect 0x108b06 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x108b06 6 14).toInstrSpec (mov_r64_r64_effect_step 0x108b06 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x108b09 [0x48, 0x29, 0xD6] (fun s => s.RIP = 0x108b09) (subR64R64Effect 0x108b09 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108b09 6 2).toInstrSpec (sub_r64_r64_effect_step 0x108b09 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x108b0c [0x49, 0xF7, 0xD6] (fun s => s.RIP = 0x108b0c) (notR64Effect 0x108b0c 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (notR64Effect_footprint 0x108b0c 14).toInstrSpec (not_r64_effect_step 0x108b0c 0x49 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x108b0f [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x108b0f) (movR64R64Effect 0x108b0f 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x108b0f 7 2).toInstrSpec (mov_r64_r64_effect_step 0x108b0f 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x108b12 [0x4C, 0x21, 0xF7] (fun s => s.RIP = 0x108b12) (andR64R64Effect 0x108b12 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108b12 7 14).toInstrSpec (and_r64_r64_effect_step 0x108b12 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x108b15 [0x49, 0x09, 0xD6] (fun s => s.RIP = 0x108b15) (orR64R64Effect 0x108b15 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108b15 14 2).toInstrSpec (or_r64_r64_effect_step 0x108b15 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x108b18 [0x48, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x108b18) (sarR64Effect 0x108b18 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (sarR64Effect_footprint 0x108b18 4 0 63).toInstrSpec (sar_r64_imm8_effect_step 0x108b18 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x108b1c [0x48, 0x01, 0xF0] (fun s => s.RIP = 0x108b1c) (addR64R64Effect 0x108b1c 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108b1c 0 6).toInstrSpec (add_r64_r64_effect_step 0x108b1c 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f80 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 111), (8, 206), (9, 139), (10, 113), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ae1) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f81 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 212), (8, 206), (9, 139), (10, 113), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ae4) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f82 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 212), (8, 214), (9, 139), (10, 113), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ae7) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f83 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 212), (8, 216), (9, 139), (10, 113), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aea) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f84 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 218), (8, 216), (9, 139), (10, 113), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aed) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f85 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 218), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108af0) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f86 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 222), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108af3) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f87 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 224), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108af6) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f88 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 226), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108afa) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.exec (n := 228) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 226), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aff) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f90 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 229), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 226), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b01) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f91 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 231), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 226), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b06) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f92 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 234) (ρ' := [(0, 231), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 233), (7, 226), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b09) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f93 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(0, 231), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 226), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b0c) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f94 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 238) (ρ' := [(0, 231), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 226), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 237), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b0f) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f95 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 231), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 239), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 237), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b12) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f96 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 231), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 237), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b15) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f97 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 231), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 243), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b18) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f98 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 245), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 243), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b1c) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 247), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (6, 235), (7, 241), (8, 216), (9, 139), (10, 220), (11, 183), (12, 156), (13, 210), (14, 243), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108b1f) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1089b2_5 code

theorem rest_l1089b2_3 [Bindings] (code : CodeMap) :
    Rest (n := 172) code lifted (codeRange 0x1089b2 bytes_l1089b2) [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 170), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]
      72 0x108a97 bytes_l1089b2_3 b_l1089b2_3 := by
  have f60 : InstrSpec 0x108a97 [0x4C, 0x89, 0x44, 0x24, 0x10] (StorePre 0x108a97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a97 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a97 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108a97 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108a97 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f61 : InstrSpec 0x108a9c [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x108a9c) (xorR32R32Effect 0x108a9c 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108a9c 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x108a9c 0x45 0xdb (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x108a9f [0x4C, 0x2B, 0x5C, 0x24, 0x10] (LoadPre 0x108a9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a9f + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108a9f 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 11, .gpr 4] [] [.reg 11, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108a9f 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x108a9f 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f63 : InstrSpec 0x108aa4 [0x49, 0x89, 0xD8] (fun s => s.RIP = 0x108aa4) (movR64R64Effect 0x108aa4 8 3)
      [.gpr 3] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108aa4 8 3).toInstrSpec (mov_r64_r64_effect_step 0x108aa4 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x108aa7 [0x4D, 0x29, 0xD0] (fun s => s.RIP = 0x108aa7) (subR64R64Effect 0x108aa7 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108aa7 8 10).toInstrSpec (sub_r64_r64_effect_step 0x108aa7 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x108aaa [0x49, 0xC1, 0xFB, 0x3F] (fun s => s.RIP = 0x108aaa) (sarR64Effect 0x108aaa 4 11 63)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (sarR64Effect_footprint 0x108aaa 4 11 63).toInstrSpec (sar_r64_imm8_effect_step 0x108aaa 0x49 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x108aae [0x4D, 0x01, 0xC3] (fun s => s.RIP = 0x108aae) (addR64R64Effect 0x108aae 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108aae 11 8).toInstrSpec (add_r64_r64_effect_step 0x108aae 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x108ab1 [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x108ab1) (notR64Effect 0x108ab1 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x108ab1 3).toInstrSpec (not_r64_effect_step 0x108ab1 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x108ab4 [0x4D, 0x89, 0xD0] (fun s => s.RIP = 0x108ab4) (movR64R64Effect 0x108ab4 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108ab4 8 10).toInstrSpec (mov_r64_r64_effect_step 0x108ab4 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x108ab7 [0x49, 0x21, 0xD8] (fun s => s.RIP = 0x108ab7) (andR64R64Effect 0x108ab7 8 3)
      [.gpr 8, .gpr 3] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108ab7 8 3).toInstrSpec (and_r64_r64_effect_step 0x108ab7 0x49 0xd8 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x108aba [0x4C, 0x09, 0xD3] (fun s => s.RIP = 0x108aba) (orR64R64Effect 0x108aba 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108aba 3 10).toInstrSpec (or_r64_r64_effect_step 0x108aba 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x108abd [0x4C, 0x21, 0xDB] (fun s => s.RIP = 0x108abd) (andR64R64Effect 0x108abd 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108abd 3 11).toInstrSpec (and_r64_r64_effect_step 0x108abd 0x4c 0xdb (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x108ac0 [0x4C, 0x09, 0xC3] (fun s => s.RIP = 0x108ac0) (orR64R64Effect 0x108ac0 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108ac0 3 8).toInstrSpec (or_r64_r64_effect_step 0x108ac0 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x108ac3 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x108ac3) (shrR64Effect 0x108ac3 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x108ac3 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x108ac3 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x108ac7 [0x48, 0x89, 0x5C, 0x24, 0x10] (StorePre 0x108ac7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108ac7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108ac7 3 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108ac7 3 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108ac7 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x108acc [0x45, 0x31, 0xED] (fun s => s.RIP = 0x108acc) (xorR32R32Effect 0x108acc 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108acc 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x108acc 0x45 0xed (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x108acf [0x4C, 0x2B, 0x6C, 0x24, 0x10] (LoadPre 0x108acf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108acf + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108acf 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108acf 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x108acf 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f77 : InstrSpec 0x108ad4 [0x49, 0x89, 0xF8] (fun s => s.RIP = 0x108ad4) (movR64R64Effect 0x108ad4 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108ad4 8 7).toInstrSpec (mov_r64_r64_effect_step 0x108ad4 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x108ad7 [0x49, 0x29, 0xC0] (fun s => s.RIP = 0x108ad7) (subR64R64Effect 0x108ad7 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108ad7 8 0).toInstrSpec (sub_r64_r64_effect_step 0x108ad7 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x108ada [0x49, 0xC1, 0xFD, 0x3F] (fun s => s.RIP = 0x108ada) (sarR64Effect 0x108ada 4 13 63)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (sarR64Effect_footprint 0x108ada 4 13 63).toInstrSpec (sar_r64_imm8_effect_step 0x108ada 0x49 0xfd 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 172) (RestInside.exec (n := 172) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 170), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a9c) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f61 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 170), (9, 139), (10, 113), (11, 173), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a9f) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f62 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 170), (9, 139), (10, 113), (11, 175), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aa4) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f63 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 177), (9, 139), (10, 113), (11, 175), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aa7) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f64 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 179), (9, 139), (10, 113), (11, 175), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aaa) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f65 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 179), (9, 139), (10, 113), (11, 181), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aae) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f66 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 179), (9, 139), (10, 113), (11, 183), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ab1) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f67 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 185), (4, 4), (5, 123), (7, 111), (8, 179), (9, 139), (10, 113), (11, 183), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ab4) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f68 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 185), (4, 4), (5, 123), (7, 111), (8, 187), (9, 139), (10, 113), (11, 183), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ab7) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f69 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 185), (4, 4), (5, 123), (7, 111), (8, 189), (9, 139), (10, 113), (11, 183), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108aba) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f70 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 191), (4, 4), (5, 123), (7, 111), (8, 189), (9, 139), (10, 113), (11, 183), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108abd) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f71 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 193), (4, 4), (5, 123), (7, 111), (8, 189), (9, 139), (10, 113), (11, 183), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ac0) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f72 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 195), (4, 4), (5, 123), (7, 111), (8, 189), (9, 139), (10, 113), (11, 183), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ac3) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f73 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 111), (8, 189), (9, 139), (10, 113), (11, 183), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ac7) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.exec (n := 199) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 111), (8, 189), (9, 139), (10, 113), (11, 183), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108acc) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f75 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 111), (8, 189), (9, 139), (10, 113), (11, 183), (12, 156), (13, 200), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108acf) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f76 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 111), (8, 189), (9, 139), (10, 113), (11, 183), (12, 156), (13, 202), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ad4) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f77 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 111), (8, 204), (9, 139), (10, 113), (11, 183), (12, 156), (13, 202), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ad7) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f78 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 111), (8, 206), (9, 139), (10, 113), (11, 183), (12, 156), (13, 202), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ada) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f79 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 197), (4, 4), (5, 123), (7, 111), (8, 206), (9, 139), (10, 113), (11, 183), (12, 156), (13, 208), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ade) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1089b2_4 code

theorem rest_l1089b2_2 [Bindings] (code : CodeMap) :
    Rest (n := 135) code lifted (codeRange 0x1089b2 bytes_l1089b2) [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 131), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]
      92 0x108a4d bytes_l1089b2_2 b_l1089b2_2 := by
  have f40 : InstrSpec 0x108a4d [0x48, 0x21, 0xEE] (fun s => s.RIP = 0x108a4d) (andR64R64Effect 0x108a4d 6 5)
      [.gpr 6, .gpr 5] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108a4d 6 5).toInstrSpec (and_r64_r64_effect_step 0x108a4d 0x48 0xee (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x108a50 [0x4C, 0x09, 0xFE] (fun s => s.RIP = 0x108a50) (orR64R64Effect 0x108a50 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108a50 6 15).toInstrSpec (or_r64_r64_effect_step 0x108a50 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x108a53 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x38] (LoadPre 0x108a53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108a53 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108a53 6 9 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x108a53 6 9 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108a53 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x108a59 [0x44, 0x88, 0x4C, 0x24, 0x0F] (StorePre 0x108a59 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x108a59 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108a59 5 9 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108a59 5 9 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108a59 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x108a5e [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x108a5e) (shrR64Effect 0x108a5e 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x108a5e 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x108a5e 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x108a62 [0x48, 0x89, 0x74, 0x24, 0x10] (StorePre 0x108a62 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a62 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a62 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108a62 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108a62 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f46 : InstrSpec 0x108a67 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x108a67) (leaR64Effect 0x108a67 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x108a67 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108a67 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x108a6c [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x108a6c) (xorR32R32Effect 0x108a6c 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108a6c 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x108a6c 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x108a6f [0x4C, 0x2B, 0x64, 0x24, 0x10] (LoadPre 0x108a6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a6f + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108a6f 12 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 12, .gpr 4] [] [.reg 12, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108a6f 12 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x108a6f 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f49 : InstrSpec 0x108a74 [0x4D, 0x89, 0xC7] (fun s => s.RIP = 0x108a74) (movR64R64Effect 0x108a74 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x108a74 15 8).toInstrSpec (mov_r64_r64_effect_step 0x108a74 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x108a77 [0x4D, 0x29, 0xDF] (fun s => s.RIP = 0x108a77) (subR64R64Effect 0x108a77 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108a77 15 11).toInstrSpec (sub_r64_r64_effect_step 0x108a77 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x108a7a [0x49, 0xC1, 0xFC, 0x3F] (fun s => s.RIP = 0x108a7a) (sarR64Effect 0x108a7a 4 12 63)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (sarR64Effect_footprint 0x108a7a 4 12 63).toInstrSpec (sar_r64_imm8_effect_step 0x108a7a 0x49 0xfc 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x108a7e [0x4D, 0x01, 0xFC] (fun s => s.RIP = 0x108a7e) (addR64R64Effect 0x108a7e 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108a7e 12 15).toInstrSpec (add_r64_r64_effect_step 0x108a7e 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x108a81 [0x49, 0xF7, 0xD0] (fun s => s.RIP = 0x108a81) (notR64Effect 0x108a81 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR64Effect_footprint 0x108a81 8).toInstrSpec (not_r64_effect_step 0x108a81 0x49 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x108a84 [0x4D, 0x89, 0xDF] (fun s => s.RIP = 0x108a84) (movR64R64Effect 0x108a84 15 11)
      [.gpr 11] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x108a84 15 11).toInstrSpec (mov_r64_r64_effect_step 0x108a84 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x108a87 [0x4D, 0x21, 0xC7] (fun s => s.RIP = 0x108a87) (andR64R64Effect 0x108a87 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108a87 15 8).toInstrSpec (and_r64_r64_effect_step 0x108a87 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x108a8a [0x4D, 0x09, 0xD8] (fun s => s.RIP = 0x108a8a) (orR64R64Effect 0x108a8a 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108a8a 8 11).toInstrSpec (or_r64_r64_effect_step 0x108a8a 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x108a8d [0x4D, 0x21, 0xE0] (fun s => s.RIP = 0x108a8d) (andR64R64Effect 0x108a8d 8 12)
      [.gpr 8, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108a8d 8 12).toInstrSpec (and_r64_r64_effect_step 0x108a8d 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x108a90 [0x4D, 0x09, 0xF8] (fun s => s.RIP = 0x108a90) (orR64R64Effect 0x108a90 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108a90 8 15).toInstrSpec (or_r64_r64_effect_step 0x108a90 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x108a93 [0x49, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x108a93) (shrR64Effect 0x108a93 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x108a93 4 8 63).toInstrSpec (shr_r64_imm8_effect_step 0x108a93 0x49 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 135), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a50) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f41 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 137), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a53) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f42 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 137), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 90), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a59) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.exec (n := 141) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 137), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 90), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a5e) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f44 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 142), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 90), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a62) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 142), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 90), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a67) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 90), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a6c) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f47 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 146), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a6f) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f48 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 148), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a74) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f49 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 148), (13, 100), (14, 133), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a77) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f50 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 148), (13, 100), (14, 133), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a7a) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f51 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 154), (13, 100), (14, 133), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a7e) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f52 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 66), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a81) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f53 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 158), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a84) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f54 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 158), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 160), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a87) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f55 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 158), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a8a) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f56 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 164), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a8d) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f57 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 166), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a90) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f58 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 168), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a93) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f59 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (7, 111), (8, 170), (9, 139), (10, 113), (11, 108), (12, 156), (13, 100), (14, 133), (15, 162), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a97) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1089b2_3 code

theorem rest_l1089b2_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x1089b2 bytes_l1089b2) [(0, 85), (1, 1), (2, 86), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (11, 88), (12, 90), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]
      112 0x108a06 bytes_l1089b2_1 b_l1089b2_1 := by
  have f20 : InstrSpec 0x108a06 [0x48, 0x8B, 0x47, 0x10] (LoadPre 0x108a06 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x108a06 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108a06 0 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108a06 0 (.base 7 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x108a06 0x48 (by decide) 0 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x108a0a [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x108a0a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108a0a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a0a 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108a0a 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x108a0a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x108a0f [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x108a0f) (mulR64Effect 0x108a0f 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x108a0f 9).toInstrSpec (mul_r64_effect_step 0x108a0f 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x108a12 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x108a12) (movR64R64Effect 0x108a12 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x108a12 10 0).toInstrSpec (mov_r64_r64_effect_step 0x108a12 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x108a15 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x108a15) (movR64R64Effect 0x108a15 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x108a15 13 2).toInstrSpec (mov_r64_r64_effect_step 0x108a15 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x108a18 [0x48, 0x8B, 0x47, 0x18] (LoadPre 0x108a18 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x108a18 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108a18 0 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x108a18 0 (.base 7 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x108a18 0x48 (by decide) 0 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x108a1c [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x108a1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108a1c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a1c 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108a1c 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x108a1c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x108a21 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x108a21) (mulR64Effect 0x108a21 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x108a21 9).toInstrSpec (mul_r64_effect_step 0x108a21 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x108a24 [0x4D, 0x01, 0xFB] (fun s => s.RIP = 0x108a24) (addR64R64Effect 0x108a24 11 15)
      [.gpr 11, .gpr 15] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108a24 11 15).toInstrSpec (add_r64_r64_effect_step 0x108a24 0x4d 0xfb (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x108a27 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x108a27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108a27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108a27 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x108a27 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x108a27 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x108a2c [0x4D, 0x11, 0xE2] (fun s => s.RIP = 0x108a2c) (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2c 10 12))
      [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x108a2c 10 12).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x108a2c 0x4d 0xe2 c (by decide) (by decide))) pre_rip
  have f31 : InstrSpec 0x108a2f [0x4C, 0x11, 0xE8] (fun s => s.RIP = 0x108a2f) (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2f 0 13))
      [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x108a2f 0 13).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x108a2f 0x4c 0xe8 c (by decide) (by decide))) pre_rip
  have f32 : InstrSpec 0x108a32 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x108a32) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x108a32 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x108a32 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x108a32 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f33 : InstrSpec 0x108a36 [0x48, 0x89, 0xF5] (fun s => s.RIP = 0x108a36) (movR64R64Effect 0x108a36 5 6)
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x108a36 5 6).toInstrSpec (mov_r64_r64_effect_step 0x108a36 0x48 0xf5 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x108a39 [0x4C, 0x29, 0xF5] (fun s => s.RIP = 0x108a39) (subR64R64Effect 0x108a39 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108a39 5 14).toInstrSpec (sub_r64_r64_effect_step 0x108a39 0x4c 0xf5 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x108a3c [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x108a3c) (notR64Effect 0x108a3c 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x108a3c 6).toInstrSpec (not_r64_effect_step 0x108a3c 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x108a3f [0x4D, 0x89, 0xF7] (fun s => s.RIP = 0x108a3f) (movR64R64Effect 0x108a3f 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x108a3f 15 14).toInstrSpec (mov_r64_r64_effect_step 0x108a3f 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x108a42 [0x49, 0x21, 0xF7] (fun s => s.RIP = 0x108a42) (andR64R64Effect 0x108a42 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108a42 15 6).toInstrSpec (and_r64_r64_effect_step 0x108a42 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x108a45 [0x4C, 0x09, 0xF6] (fun s => s.RIP = 0x108a45) (orR64R64Effect 0x108a45 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108a45 6 14).toInstrSpec (or_r64_r64_effect_step 0x108a45 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x108a48 [0x4C, 0x8B, 0x74, 0x24, 0x30] (LoadPre 0x108a48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108a48 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108a48 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x108a48 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x108a48 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 1), (2, 86), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (11, 88), (12, 90), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a0a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 92), (1, 1), (2, 86), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (11, 88), (12, 90), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a0f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 96) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 97) (ρ' := [(0, 95), (1, 1), (2, 96), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (11, 88), (12, 90), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a12) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 1), (2, 96), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 98), (11, 88), (12, 90), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a15) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 95), (1, 1), (2, 96), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 98), (11, 88), (12, 90), (13, 100), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a18) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 102), (1, 1), (2, 96), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 98), (11, 88), (12, 90), (13, 100), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a1c) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 102), (1, 1), (2, 96), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 98), (11, 88), (12, 90), (13, 100), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a21) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 106) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 107) (ρ' := [(0, 105), (1, 1), (2, 106), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 98), (11, 88), (12, 90), (13, 100), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a24) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 109) f28 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 110) (ρ' := [(0, 105), (1, 1), (2, 106), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 98), (11, 108), (12, 90), (13, 100), (14, 80), (15, 78), (16, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a27) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 105), (1, 1), (2, 106), (3, 68), (4, 4), (6, 56), (7, 111), (8, 66), (9, 64), (10, 98), (11, 108), (12, 90), (13, 100), (14, 80), (15, 78), (16, 109), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a2c) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 114) f30 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x108a2c 10 12 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 115) (ρ' := [(0, 105), (1, 1), (2, 106), (3, 68), (4, 4), (6, 56), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 80), (15, 78), (16, 114), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a2f) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 117) f31 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x108a2f 0 13 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 118) (ρ' := [(0, 116), (1, 1), (2, 106), (3, 68), (4, 4), (6, 56), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 80), (15, 78), (16, 117), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a32) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (6, 56), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a36) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f33 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 121), (6, 56), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a39) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f34 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 56), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a3c) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f35 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 125), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a3f) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f36 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 125), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 80), (15, 127), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a42) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f37 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 125), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 80), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a45) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f38 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 131), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 80), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a48) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f39 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 116), (1, 1), (2, 119), (3, 68), (4, 4), (5, 123), (6, 131), (7, 111), (8, 66), (9, 64), (10, 113), (11, 108), (12, 90), (13, 100), (14, 133), (15, 129), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a4d) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1089b2_2 code

theorem rest_l1089b2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1089b2 bytes_l1089b2) (entryMap (live .l1089b2))
      132 0x1089b2 bytes_l1089b2 b_l1089b2 := by
  have f0 : InstrSpec 0x1089b2 [0x48, 0x89, 0x5C, 0x24, 0x70] (StorePre 0x1089b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1089b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1089b2 3 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1089b2 3 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1089b2 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1089b7 [0x48, 0x8B, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x1089b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1089b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1089b7 7 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1089b7 7 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x1089b7 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1089bf [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x1089bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1089bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1089bf 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1089bf 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1089bf 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1089c4 [0x4C, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x1089c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1089c4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1089c4 9 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1089c4 9 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x1089c4 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1089cc [0x4C, 0x0F, 0xAF, 0xCE] (fun s => s.RIP = 0x1089cc) (imulR64R64Effect 0x1089cc 4 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x1089cc 4 9 6).toInstrSpec (imul_r64_r64_effect_step 0x1089cc 0x4c (by decide) 0xce (by decide)) pre_rip
  have f5 : InstrSpec 0x1089d0 [0x49, 0xD3, 0xE1] (fun s => s.RIP = 0x1089d0) (shlR64ClEffect 0x1089d0 3 9)
      [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x1089d0 3 9).toInstrSpec (shl_r64_cl_effect_step 0x1089d0 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1089d3 [0x49, 0xD3, 0xE9] (fun s => s.RIP = 0x1089d3) (shrR64ClEffect 0x1089d3 3 9)
      [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x1089d3 3 9).toInstrSpec (shr_r64_cl_effect_step 0x1089d3 0x49 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1089d6 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1089d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1089d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1089d6 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1089d6 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1089d6 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1089db [0x48, 0x8B, 0x5C, 0x24, 0x20] (LoadPre 0x1089db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1089db + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1089db 3 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1089db 3 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1089db 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1089e0 [0x48, 0x8B, 0x07] (LoadPre 0x1089e0 (fun s => AddrMode.addr (.base 7 .none) s (0x1089e0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1089e0 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1089e0 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1089e0 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1089e3 [0x4C, 0x8B, 0x57, 0x08] (LoadPre 0x1089e3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1089e3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1089e3 10 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1089e3 10 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1089e3 0x4c (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1089e7 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x1089e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1089e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1089e7 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1089e7 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x1089e7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1089ec [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x1089ec) (mulR64Effect 0x1089ec 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1089ec 9).toInstrSpec (mul_r64_effect_step 0x1089ec 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1089ef [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x1089ef) (movR64R64Effect 0x1089ef 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1089ef 15 2).toInstrSpec (mov_r64_r64_effect_step 0x1089ef 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1089f2 [0x49, 0x89, 0xC6] (fun s => s.RIP = 0x1089f2) (movR64R64Effect 0x1089f2 14 0)
      [.gpr 0] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1089f2 14 0).toInstrSpec (mov_r64_r64_effect_step 0x1089f2 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1089f5 [0x4C, 0x89, 0x54, 0x24, 0x58] (StorePre 0x1089f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1089f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1089f5 10 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1089f5 10 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1089f5 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1089fa [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x1089fa) (movR64R64Effect 0x1089fa 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1089fa 0 10).toInstrSpec (mov_r64_r64_effect_step 0x1089fa 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1089fd [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x1089fd) (mulR64Effect 0x1089fd 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x1089fd 9).toInstrSpec (mul_r64_effect_step 0x1089fd 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x108a00 [0x49, 0x89, 0xC3] (fun s => s.RIP = 0x108a00) (movR64R64Effect 0x108a00 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x108a00 11 0).toInstrSpec (mov_r64_r64_effect_step 0x108a00 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x108a03 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x108a03) (movR64R64Effect 0x108a03 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x108a03 12 2).toInstrSpec (mov_r64_r64_effect_step 0x108a03 0x49 0xd4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089b7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (3, 3), (4, 4), (7, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089bf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089c4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (9, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089cc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (9, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089d0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (9, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089d3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (9, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089d6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 1), (3, 3), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089db) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 1), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089e0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 1), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089e3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 1), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089e7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 1), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089ec) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 76), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089ef) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 75), (1, 1), (2, 76), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089f2) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 75), (1, 1), (2, 76), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089f5) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 75), (1, 1), (2, 76), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089fa) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (2, 76), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1089fd) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 85), (1, 1), (2, 86), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a00) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 85), (1, 1), (2, 86), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (11, 88), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a03) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 85), (1, 1), (2, 86), (3, 68), (4, 4), (6, 56), (7, 54), (8, 66), (9, 64), (10, 72), (11, 88), (12, 90), (14, 80), (15, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108a06) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1089b2_1 code

theorem block_l1089b2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1089b2 :=
  Rest.liftedBlock (rest_l1089b2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1089b2 x hx)

theorem rest_l108bb1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108bb1 bytes_l108bb1) (entryMap (live .l108bb1))
      3 0x108bb1 bytes_l108bb1 b_l108bb1 := by
  have f0 : InstrSpec 0x108bb1 [0x44, 0x88, 0x4C, 0x24, 0x0E] (StorePre 0x108bb1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x108bb1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108bb1 5 9 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108bb1 5 9 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108bb1 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x108bb6 [0x83, 0x7C, 0x24, 0x44, 0x00] (LoadPre 0x108bb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x108bb6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x108bb6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x108bb6 5 (.sib 4 none 0 (.d8 0x44)) 0x0).toInstrSpec (cmp_m32_imm8_effect_step 0x108bb6 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bb6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bbb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x108bbb 4 0x250) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l108bb1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108bb1 :=
  Rest.liftedBlock (rest_l108bb1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108bb1 x hx)

theorem rest_l108bc1_8 [Bindings] (code : CodeMap) :
    Rest (n := 358) code lifted (codeRange 0x108bc1 bytes_l108bc1) [(0, 330), (1, 352), (2, 341), (3, 324), (4, 4), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x108dde bytes_l108bc1_8 b_l108bc1_8 := by
  have f160 : InstrSpec 0x108dde [0x48, 0x89, 0x56, 0x10] (StorePre 0x108dde 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108dde + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108dde 2 (.base 6 (.d8 0x10)))
      [.gpr 2, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x108dde 2 (.base 6 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108dde 0x48 (by decide) 2 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f161 : InstrSpec 0x108de2 [0x48, 0x89, 0x4E, 0x18] (StorePre 0x108de2 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108de2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108de2 1 (.base 6 (.d8 0x18)))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x108de2 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x108de2 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f162 : InstrSpec 0x108de6 [0x40, 0x88, 0x6E, 0x20] (StorePre 0x108de6 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x108de6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108de6 4 5 (.base 6 (.d8 0x20)))
      [.gpr 5, .gpr 6] [] [.rip] :=
    (movM8R8Effect_footprint 0x108de6 4 5 (.base 6 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x108de6 0x40 (by decide) 5 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f163 : InstrSpec 0x108dea [0x48, 0x83, 0xC4, 0x78] (fun s => s.RIP = 0x108dea) (addR64Imm8Effect 0x108dea 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x108dea 4 0x78).toInstrSpec (add_r64_imm8_effect_step 0x108dea 0x48 0xc4 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f164 : InstrSpec 0x108dee [0x5B] (PopPre 0x108dee) (popR64Effect 0x108dee 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108dee 1 3).toInstrSpec (pop_r64_effect_step 0x108dee 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f165 : InstrSpec 0x108def [0x41, 0x5C] (PopPre 0x108def) (popR64Effect 0x108def 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108def 2 12).toInstrSpec (pop_r64_rex_effect_step 0x108def 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f166 : InstrSpec 0x108df1 [0x41, 0x5D] (PopPre 0x108df1) (popR64Effect 0x108df1 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108df1 2 13).toInstrSpec (pop_r64_rex_effect_step 0x108df1 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f167 : InstrSpec 0x108df3 [0x41, 0x5E] (PopPre 0x108df3) (popR64Effect 0x108df3 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108df3 2 14).toInstrSpec (pop_r64_rex_effect_step 0x108df3 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f168 : InstrSpec 0x108df5 [0x41, 0x5F] (PopPre 0x108df5) (popR64Effect 0x108df5 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108df5 2 15).toInstrSpec (pop_r64_rex_effect_step 0x108df5 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f169 : InstrSpec 0x108df7 [0x5D] (PopPre 0x108df7) (popR64Effect 0x108df7 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108df7 1 5).toInstrSpec (pop_r64_effect_step 0x108df7 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f170 : InstrSpec 0x108df8 [0xC3] (RetPre 0x108df8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x108df8).toInstrSpec (ret_effect_step 0x108df8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 358) (RestInside.exec (n := 358) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 324), (4, 4), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108de2) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 359) (RestInside.exec (n := 359) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 324), (4, 4), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108de6) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 360) (RestInside.exec (n := 360) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 324), (4, 4), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dea) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f163 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 324), (4, 361), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dee) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 363) (RestInside.out (n := 363) f164 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 364) f164 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 365) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 363), (4, 364), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108def) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 366) (RestInside.out (n := 366) f165 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 367) f165 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 368) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 363), (4, 367), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 366), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108df1) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 369) (RestInside.out (n := 369) f166 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 370) f166 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 371) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 363), (4, 370), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 366), (13, 369), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108df3) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 372) (RestInside.out (n := 372) f167 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 373) f167 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 374) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 363), (4, 373), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 366), (13, 369), (14, 372), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108df5) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 375) (RestInside.out (n := 375) f168 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 376) f168 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 377) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 363), (4, 376), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 366), (13, 369), (14, 372), (15, 375), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108df7) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f169 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 379) f169 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 380) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 363), (4, 379), (5, 378), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 366), (13, 369), (14, 372), (15, 375), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108df8) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 381) (RestInside.out (n := 381) f170 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 382) f170 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 383) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 363), (4, 382), (5, 378), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 366), (13, 369), (14, 372), (15, 375), (22, 22), (39, 39), (50, 50), (51, 51)]) f170 (by decide) rfl rfl rfl (by decide)

theorem rest_l108bc1_7 [Bindings] (code : CodeMap) :
    Rest (n := 322) code lifted (codeRange 0x108bc1 bytes_l108bc1) [(0, 159), (1, 290), (2, 313), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]
      31 0x108d97 bytes_l108bc1_7 b_l108bc1_7 := by
  have f140 : InstrSpec 0x108d97 [0x0F, 0xB6, 0x44, 0x24, 0x10] (LoadPre 0x108d97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d97 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108d97 5 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x108d97 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x108d97 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f141 : InstrSpec 0x108d9c [0x4C, 0x31, 0xCB] (fun s => s.RIP = 0x108d9c) (xorR64R64Effect 0x108d9c 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108d9c 3 9).toInstrSpec (xor_r64_r64_effect_step 0x108d9c 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x108d9f [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x108d9f) (negR64Effect 0x108d9f 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x108d9f 0).toInstrSpec (neg_r64_effect_step 0x108d9f 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x108da2 [0x48, 0x21, 0xD8] (fun s => s.RIP = 0x108da2) (andR64R64Effect 0x108da2 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108da2 0 3).toInstrSpec (and_r64_r64_effect_step 0x108da2 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x108da5 [0x4C, 0x31, 0xC8] (fun s => s.RIP = 0x108da5) (xorR64R64Effect 0x108da5 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108da5 0 9).toInstrSpec (xor_r64_r64_effect_step 0x108da5 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f145 : InstrSpec 0x108da8 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x108da8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108da8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108da8 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108da8 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x108da8 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f146 : InstrSpec 0x108dac [0x0F, 0xB6, 0x54, 0x24, 0x10] (LoadPre 0x108dac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108dac + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108dac 5 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x108dac 5 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x108dac 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f147 : InstrSpec 0x108db1 [0x49, 0x31, 0xF4] (fun s => s.RIP = 0x108db1) (xorR64R64Effect 0x108db1 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108db1 12 6).toInstrSpec (xor_r64_r64_effect_step 0x108db1 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x108db4 [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x108db4) (negR64Effect 0x108db4 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x108db4 2).toInstrSpec (neg_r64_effect_step 0x108db4 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f149 : InstrSpec 0x108db7 [0x4C, 0x21, 0xE2] (fun s => s.RIP = 0x108db7) (andR64R64Effect 0x108db7 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108db7 2 12).toInstrSpec (and_r64_r64_effect_step 0x108db7 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x108dba [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x108dba) (xorR64R64Effect 0x108dba 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108dba 2 6).toInstrSpec (xor_r64_r64_effect_step 0x108dba 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x108dbd [0x88, 0x4C, 0x24, 0x10] (StorePre 0x108dbd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108dbd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108dbd 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108dbd 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x108dbd 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f152 : InstrSpec 0x108dc1 [0x0F, 0xB6, 0x4C, 0x24, 0x10] (LoadPre 0x108dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108dc1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108dc1 5 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x108dc1 5 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x108dc1 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f153 : InstrSpec 0x108dc6 [0x49, 0x31, 0xFB] (fun s => s.RIP = 0x108dc6) (xorR64R64Effect 0x108dc6 11 7)
      [.gpr 11, .gpr 7] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108dc6 11 7).toInstrSpec (xor_r64_r64_effect_step 0x108dc6 0x49 0xfb (by decide) (by decide)) pre_rip
  have f154 : InstrSpec 0x108dc9 [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x108dc9) (negR64Effect 0x108dc9 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x108dc9 1).toInstrSpec (neg_r64_effect_step 0x108dc9 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x108dcc [0x4C, 0x21, 0xD9] (fun s => s.RIP = 0x108dcc) (andR64R64Effect 0x108dcc 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108dcc 1 11).toInstrSpec (and_r64_r64_effect_step 0x108dcc 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x108dcf [0x48, 0x31, 0xF9] (fun s => s.RIP = 0x108dcf) (xorR64R64Effect 0x108dcf 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108dcf 1 7).toInstrSpec (xor_r64_r64_effect_step 0x108dcf 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x108dd2 [0x48, 0x8B, 0x74, 0x24, 0x70] (LoadPre 0x108dd2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x108dd2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108dd2 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x108dd2 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x108dd2 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f158 : InstrSpec 0x108dd7 [0x4C, 0x89, 0x06] (StorePre 0x108dd7 3 (fun s => AddrMode.addr (.base 6 .none) s (0x108dd7 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x108dd7 8 (.base 6 .none))
      [.gpr 8, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x108dd7 8 (.base 6 .none)).toInstrSpec (mov_m64_r64_effect_step 0x108dd7 0x4c (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f159 : InstrSpec 0x108dda [0x48, 0x89, 0x46, 0x08] (StorePre 0x108dda 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108dda + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108dda 0 (.base 6 (.d8 0x8)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM64R64Effect_footprint 0x108dda 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x108dda 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f140 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 322), (1, 290), (2, 313), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d9c) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f141 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 322), (1, 290), (2, 313), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d9f) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f142 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 326), (1, 290), (2, 313), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108da2) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f143 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 329) (ρ' := [(0, 328), (1, 290), (2, 313), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108da5) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f144 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 330), (1, 290), (2, 313), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108da8) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.exec (n := 332) (ρ' := [(0, 330), (1, 290), (2, 313), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dac) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 333) (RestInside.out (n := 333) f146 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 334) (ρ' := [(0, 330), (1, 290), (2, 333), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108db1) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 335) (RestInside.out (n := 335) f147 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 336) (ρ' := [(0, 330), (1, 290), (2, 333), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108db4) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 337) (RestInside.out (n := 337) f148 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 338) (ρ' := [(0, 330), (1, 290), (2, 337), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108db7) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 339) (RestInside.out (n := 339) f149 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 340) (ρ' := [(0, 330), (1, 290), (2, 339), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dba) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f150 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 342) (ρ' := [(0, 330), (1, 290), (2, 341), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dbd) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 343) (RestInside.exec (n := 343) (ρ' := [(0, 330), (1, 290), (2, 341), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dc1) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f152 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 330), (1, 344), (2, 341), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dc6) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.out (n := 346) f153 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 347) (ρ' := [(0, 330), (1, 344), (2, 341), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dc9) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f154 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 349) (ρ' := [(0, 330), (1, 348), (2, 341), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dcc) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 350) (RestInside.out (n := 350) f155 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 351) (ρ' := [(0, 330), (1, 350), (2, 341), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dcf) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 352) (RestInside.out (n := 352) f156 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 353) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 324), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dd2) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 354) (RestInside.out (n := 354) f157 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 355) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 324), (4, 4), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dd7) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 356) (RestInside.exec (n := 356) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 324), (4, 4), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dda) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 357) (RestInside.exec (n := 357) (ρ' := [(0, 330), (1, 352), (2, 341), (3, 324), (4, 4), (5, 284), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 335), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108dde) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l108bc1_8 code

theorem rest_l108bc1_6 [Bindings] (code : CodeMap) :
    Rest (n := 288) code lifted (codeRange 0x108bc1 bytes_l108bc1) [(0, 159), (1, 276), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 263), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (19, 286), (22, 22), (39, 39), (50, 50), (51, 51)]
      51 0x108d48 bytes_l108bc1_6 b_l108bc1_6 := by
  have f120 : InstrSpec 0x108d48 [0x0F, 0x94, 0xC1] (fun s => s.RIP = 0x108d48) (atFlags (condHolds 4) (setccR8Effect 0x108d48 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x108d48 3 1 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x108d48 4 0xc1 (by decide) (by decide) c)) pre_rip
  have f121 : InstrSpec 0x108d4b [0x44, 0x20, 0xC1] (fun s => s.RIP = 0x108d4b) (andR8R8Effect 0x108d4b 3 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (andR8R8Effect_footprint 0x108d4b 3 1 8).toInstrSpec (and_r8_r8_rex_effect_step 0x108d4b 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x108d4e [0x88, 0x4C, 0x24, 0x10] (StorePre 0x108d4e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d4e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108d4e 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d4e 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x108d4e 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f123 : InstrSpec 0x108d52 [0x4C, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x108d52) (leaR64Effect 0x108d52 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x108d52 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108d52 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x108d57 [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x10] (LoadPre 0x108d57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d57 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d57 6 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x108d57 6 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d57 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f125 : InstrSpec 0x108d5d [0x49, 0xFF, 0xCA] (fun s => s.RIP = 0x108d5d) (decR64Effect 0x108d5d 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (decR64Effect_footprint 0x108d5d 10).toInstrSpec (dec_r64_effect_step 0x108d5d 0x49 0xca (by decide) (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x108d60 [0x4D, 0x21, 0xC2] (fun s => s.RIP = 0x108d60) (andR64R64Effect 0x108d60 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108d60 10 8).toInstrSpec (and_r64_r64_effect_step 0x108d60 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f127 : InstrSpec 0x108d63 [0x49, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x108d63) (sarR64Effect 0x108d63 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (sarR64Effect_footprint 0x108d63 4 10 63).toInstrSpec (sar_r64_imm8_effect_step 0x108d63 0x49 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f128 : InstrSpec 0x108d67 [0x4D, 0x01, 0xEA] (fun s => s.RIP = 0x108d67) (addR64R64Effect 0x108d67 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108d67 10 13).toInstrSpec (add_r64_r64_effect_step 0x108d67 0x4d 0xea (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x108d6a [0x49, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x108d6a) (shrR64Effect 0x108d6a 4 10 63)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x108d6a 4 10 63).toInstrSpec (shr_r64_imm8_effect_step 0x108d6a 0x49 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f130 : InstrSpec 0x108d6e [0x4C, 0x89, 0x54, 0x24, 0x10] (StorePre 0x108d6e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d6e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108d6e 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108d6e 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108d6e 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f131 : InstrSpec 0x108d73 [0x4C, 0x8D, 0x44, 0x24, 0x10] (fun s => s.RIP = 0x108d73) (leaR64Effect 0x108d73 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x108d73 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108d73 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x108d78 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x108d78 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d78 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108d78 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d78 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x108d78 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f133 : InstrSpec 0x108d7c [0x4C, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x108d7c) (leaR64Effect 0x108d7c 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x108d7c 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108d7c 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f134 : InstrSpec 0x108d81 [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x10] (LoadPre 0x108d81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d81 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d81 6 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M8Effect_footprint 0x108d81 6 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108d81 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f135 : InstrSpec 0x108d87 [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x108d87) (xorR64R64Effect 0x108d87 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108d87 2 0).toInstrSpec (xor_r64_r64_effect_step 0x108d87 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x108d8a [0x49, 0xF7, 0xD8] (fun s => s.RIP = 0x108d8a) (negR64Effect 0x108d8a 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR64Effect_footprint 0x108d8a 8).toInstrSpec (neg_r64_effect_step 0x108d8a 0x49 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x108d8d [0x49, 0x21, 0xD0] (fun s => s.RIP = 0x108d8d) (andR64R64Effect 0x108d8d 8 2)
      [.gpr 8, .gpr 2] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108d8d 8 2).toInstrSpec (and_r64_r64_effect_step 0x108d8d 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f138 : InstrSpec 0x108d90 [0x49, 0x31, 0xC0] (fun s => s.RIP = 0x108d90) (xorR64R64Effect 0x108d90 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108d90 8 0).toInstrSpec (xor_r64_r64_effect_step 0x108d90 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f139 : InstrSpec 0x108d93 [0x88, 0x4C, 0x24, 0x10] (StorePre 0x108d93 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d93 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108d93 4 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x108d93 4 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x108d93 1 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f120 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 159), (1, 288), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 263), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (19, 286), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d4b) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f121 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 263), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d4e) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.exec (n := 292) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 263), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d52) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 293) (RestInside.exec (n := 293) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d57) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f124 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 295) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 294), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d5d) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.out (n := 296) f125 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 297) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 296), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d60) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f126 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 298), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d63) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f127 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 300), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d67) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f128 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 302), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d6a) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f129 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 304), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d6e) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.exec (n := 306) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 304), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d73) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 307) (RestInside.exec (n := 307) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (9, 191), (10, 304), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d78) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 308) (RestInside.exec (n := 308) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (9, 191), (10, 304), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d7c) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f133 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d81) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f134 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 159), (1, 290), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 311), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d87) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f135 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 314) (ρ' := [(0, 159), (1, 290), (2, 313), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 311), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d8a) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 315) (RestInside.out (n := 315) f136 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 316) (ρ' := [(0, 159), (1, 290), (2, 313), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 315), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d8d) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 317) (RestInside.out (n := 317) f137 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 318) (ρ' := [(0, 159), (1, 290), (2, 313), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 317), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d90) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 319) (RestInside.out (n := 319) f138 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 320) (ρ' := [(0, 159), (1, 290), (2, 313), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d93) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 321) (RestInside.exec (n := 321) (ρ' := [(0, 159), (1, 290), (2, 313), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 319), (9, 191), (10, 309), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d97) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l108bc1_7 code

theorem rest_l108bc1_5 [Bindings] (code : CodeMap) :
    Rest (n := 249) code lifted (codeRange 0x108bc1 bytes_l108bc1) [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 243), (8, 247), (9, 191), (10, 101), (11, 245), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]
      71 0x108d01 bytes_l108bc1_5 b_l108bc1_5 := by
  have f100 : InstrSpec 0x108d01 [0x4C, 0x8B, 0x74, 0x24, 0x68] (LoadPre 0x108d01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108d01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108d01 14 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x108d01 14 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x108d01 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f101 : InstrSpec 0x108d06 [0x4D, 0x29, 0xF0] (fun s => s.RIP = 0x108d06) (subR64R64Effect 0x108d06 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108d06 8 14).toInstrSpec (sub_r64_r64_effect_step 0x108d06 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x108d09 [0x48, 0xC1, 0xFF, 0x3F] (fun s => s.RIP = 0x108d09) (sarR64Effect 0x108d09 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (sarR64Effect_footprint 0x108d09 4 7 63).toInstrSpec (sar_r64_imm8_effect_step 0x108d09 0x48 0xff 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x108d0d [0x4C, 0x01, 0xC7] (fun s => s.RIP = 0x108d0d) (addR64R64Effect 0x108d0d 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108d0d 7 8).toInstrSpec (add_r64_r64_effect_step 0x108d0d 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x108d10 [0x4D, 0x89, 0xD8] (fun s => s.RIP = 0x108d10) (movR64R64Effect 0x108d10 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108d10 8 11).toInstrSpec (mov_r64_r64_effect_step 0x108d10 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x108d13 [0x49, 0xF7, 0xD0] (fun s => s.RIP = 0x108d13) (notR64Effect 0x108d13 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR64Effect_footprint 0x108d13 8).toInstrSpec (not_r64_effect_step 0x108d13 0x49 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x108d16 [0x4D, 0x89, 0xF2] (fun s => s.RIP = 0x108d16) (movR64R64Effect 0x108d16 10 14)
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x108d16 10 14).toInstrSpec (mov_r64_r64_effect_step 0x108d16 0x4d 0xf2 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x108d19 [0x4D, 0x21, 0xC2] (fun s => s.RIP = 0x108d19) (andR64R64Effect 0x108d19 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108d19 10 8).toInstrSpec (and_r64_r64_effect_step 0x108d19 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x108d1c [0x4D, 0x09, 0xF0] (fun s => s.RIP = 0x108d1c) (orR64R64Effect 0x108d1c 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108d1c 8 14).toInstrSpec (or_r64_r64_effect_step 0x108d1c 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x108d1f [0x49, 0x21, 0xF8] (fun s => s.RIP = 0x108d1f) (andR64R64Effect 0x108d1f 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108d1f 8 7).toInstrSpec (and_r64_r64_effect_step 0x108d1f 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x108d22 [0x4D, 0x09, 0xD0] (fun s => s.RIP = 0x108d22) (orR64R64Effect 0x108d22 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108d22 8 10).toInstrSpec (or_r64_r64_effect_step 0x108d22 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x108d25 [0x49, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x108d25) (shrR64Effect 0x108d25 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x108d25 4 8 63).toInstrSpec (shr_r64_imm8_effect_step 0x108d25 0x49 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x108d29 [0x4C, 0x89, 0x44, 0x24, 0x10] (StorePre 0x108d29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108d29 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108d29 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108d29 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f113 : InstrSpec 0x108d2e [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x108d2e) (xorR32R32Effect 0x108d2e 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108d2e 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x108d2e 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x108d31 [0x89, 0xE9] (fun s => s.RIP = 0x108d31) (movR32R32Effect 0x108d31 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108d31 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x108d31 0xe9 (by decide)) pre_rip
  have f115 : InstrSpec 0x108d33 [0x49, 0xD3, 0xED] (fun s => s.RIP = 0x108d33) (shrR64ClEffect 0x108d33 3 13)
      [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x108d33 3 13).toInstrSpec (shr_r64_cl_effect_step 0x108d33 0x49 0xed (by decide) (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x108d36 [0x4C, 0x2B, 0x44, 0x24, 0x10] (LoadPre 0x108d36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d36 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108d36 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108d36 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x108d36 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f117 : InstrSpec 0x108d3b [0x0F, 0xB6, 0x6C, 0x24, 0x0F] (LoadPre 0x108d3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x108d3b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108d3b 5 5 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x108d3b 5 5 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x108d3b 5 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f118 : InstrSpec 0x108d40 [0x40, 0x32, 0x6C, 0x24, 0x0E] (LoadPre 0x108d40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x108d40 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108d40 5 5 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 5, .gpr 4] [] [.reg 5, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x108d40 5 5 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (xor_r8_m8_rex_effect_step 0x108d40 0x40 (by decide) 5 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f119 : InstrSpec 0x108d45 [0x4D, 0x85, 0xED] (fun s => s.RIP = 0x108d45) (testR64R64Effect 0x108d45 13 13)
      [.gpr 13, .gpr 13] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x108d45 13 13).toInstrSpec (test_r64_r64_effect_step 0x108d45 0x4d 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f100 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 243), (8, 247), (9, 191), (10, 101), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d06) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f101 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 243), (8, 251), (9, 191), (10, 101), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d09) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f102 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 253), (8, 251), (9, 191), (10, 101), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d0d) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f103 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 251), (9, 191), (10, 101), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d10) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f104 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 257), (9, 191), (10, 101), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d13) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f105 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 259), (9, 191), (10, 101), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d16) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f106 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 259), (9, 191), (10, 261), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d19) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f107 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 259), (9, 191), (10, 263), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d1c) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f108 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 265), (9, 191), (10, 263), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d1f) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f109 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 267), (9, 191), (10, 263), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d22) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.out (n := 269) f110 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 270) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 269), (9, 191), (10, 263), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d25) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.out (n := 271) f111 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 272) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 271), (9, 191), (10, 263), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d29) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.exec (n := 273) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 271), (9, 191), (10, 263), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d2e) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f113 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 274), (9, 191), (10, 263), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d31) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f114 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 159), (1, 276), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 274), (9, 191), (10, 263), (11, 245), (12, 131), (13, 93), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d33) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f115 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 159), (1, 276), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 274), (9, 191), (10, 263), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d36) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f116 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 159), (1, 276), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 255), (8, 280), (9, 191), (10, 263), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d3b) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f117 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 159), (1, 276), (2, 153), (3, 151), (4, 4), (5, 282), (6, 222), (7, 255), (8, 280), (9, 191), (10, 263), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d40) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f118 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 159), (1, 276), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 263), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d45) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f119 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 159), (1, 276), (2, 153), (3, 151), (4, 4), (5, 284), (6, 222), (7, 255), (8, 280), (9, 191), (10, 263), (11, 245), (12, 131), (13, 278), (14, 249), (15, 145), (19, 286), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d48) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108bc1_6 code

theorem rest_l108bc1_4 [Bindings] (code : CodeMap) :
    Rest (n := 210) code lifted (codeRange 0x108bc1 bytes_l108bc1) [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 207), (7, 199), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]
      91 0x108cbd bytes_l108bc1_4 b_l108bc1_4 := by
  have f80 : InstrSpec 0x108cbd [0x31, 0xF6] (fun s => s.RIP = 0x108cbd) (xorR32R32Effect 0x108cbd 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108cbd 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x108cbd 0xf6 (by decide)) pre_rip
  have f81 : InstrSpec 0x108cbf [0x48, 0x2B, 0x74, 0x24, 0x10] (LoadPre 0x108cbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cbf + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108cbf 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108cbf 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x108cbf 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f82 : InstrSpec 0x108cc4 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x108cc4) (movR64R64Effect 0x108cc4 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x108cc4 7 12).toInstrSpec (mov_r64_r64_effect_step 0x108cc4 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x108cc7 [0x4C, 0x8B, 0x74, 0x24, 0x60] (LoadPre 0x108cc7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108cc7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108cc7 14 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x108cc7 14 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x108cc7 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f84 : InstrSpec 0x108ccc [0x4C, 0x29, 0xF7] (fun s => s.RIP = 0x108ccc) (subR64R64Effect 0x108ccc 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108ccc 7 14).toInstrSpec (sub_r64_r64_effect_step 0x108ccc 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x108ccf [0x48, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x108ccf) (sarR64Effect 0x108ccf 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (sarR64Effect_footprint 0x108ccf 4 6 63).toInstrSpec (sar_r64_imm8_effect_step 0x108ccf 0x48 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x108cd3 [0x48, 0x01, 0xFE] (fun s => s.RIP = 0x108cd3) (addR64R64Effect 0x108cd3 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108cd3 6 7).toInstrSpec (add_r64_r64_effect_step 0x108cd3 0x48 0xfe (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x108cd6 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x108cd6) (movR64R64Effect 0x108cd6 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x108cd6 7 12).toInstrSpec (mov_r64_r64_effect_step 0x108cd6 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x108cd9 [0x48, 0xF7, 0xD7] (fun s => s.RIP = 0x108cd9) (notR64Effect 0x108cd9 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (notR64Effect_footprint 0x108cd9 7).toInstrSpec (not_r64_effect_step 0x108cd9 0x48 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x108cdc [0x4D, 0x89, 0xF0] (fun s => s.RIP = 0x108cdc) (movR64R64Effect 0x108cdc 8 14)
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108cdc 8 14).toInstrSpec (mov_r64_r64_effect_step 0x108cdc 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x108cdf [0x49, 0x21, 0xF8] (fun s => s.RIP = 0x108cdf) (andR64R64Effect 0x108cdf 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108cdf 8 7).toInstrSpec (and_r64_r64_effect_step 0x108cdf 0x49 0xf8 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x108ce2 [0x4C, 0x09, 0xF7] (fun s => s.RIP = 0x108ce2) (orR64R64Effect 0x108ce2 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108ce2 7 14).toInstrSpec (or_r64_r64_effect_step 0x108ce2 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x108ce5 [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x108ce5) (andR64R64Effect 0x108ce5 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108ce5 7 6).toInstrSpec (and_r64_r64_effect_step 0x108ce5 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x108ce8 [0x4C, 0x09, 0xC7] (fun s => s.RIP = 0x108ce8) (orR64R64Effect 0x108ce8 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108ce8 7 8).toInstrSpec (or_r64_r64_effect_step 0x108ce8 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x108ceb [0x48, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x108ceb) (shrR64Effect 0x108ceb 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x108ceb 4 7 63).toInstrSpec (shr_r64_imm8_effect_step 0x108ceb 0x48 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x108cef [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x108cef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108cef 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108cef 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108cef 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x108cf4 [0x31, 0xFF] (fun s => s.RIP = 0x108cf4) (xorR32R32Effect 0x108cf4 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108cf4 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x108cf4 0xff (by decide)) pre_rip
  have f97 : InstrSpec 0x108cf6 [0x48, 0x2B, 0x7C, 0x24, 0x10] (LoadPre 0x108cf6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cf6 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108cf6 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108cf6 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x108cf6 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f98 : InstrSpec 0x108cfb [0x4D, 0x09, 0xD3] (fun s => s.RIP = 0x108cfb) (orR64R64Effect 0x108cfb 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108cfb 11 10).toInstrSpec (or_r64_r64_effect_step 0x108cfb 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x108cfe [0x4D, 0x89, 0xD8] (fun s => s.RIP = 0x108cfe) (movR64R64Effect 0x108cfe 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108cfe 8 11).toInstrSpec (mov_r64_r64_effect_step 0x108cfe 0x4d 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f80 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 210), (7, 199), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cbf) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f81 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 212), (7, 199), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cc4) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f82 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 212), (7, 214), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cc7) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f83 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 212), (7, 214), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ccc) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f84 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 212), (7, 218), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ccf) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f85 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 220), (7, 218), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cd3) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f86 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 218), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cd6) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f87 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 224), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cd9) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f88 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 226), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cdc) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f89 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 229) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 226), (8, 228), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cdf) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f90 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 226), (8, 230), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ce2) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f91 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 232), (8, 230), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ce5) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f92 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 234), (8, 230), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ce8) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f93 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 236), (8, 230), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ceb) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f94 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 238), (8, 230), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cef) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.exec (n := 240) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 238), (8, 230), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cf4) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f96 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 241), (8, 230), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cf6) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f97 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 243), (8, 230), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cfb) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f98 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 243), (8, 230), (9, 191), (10, 101), (11, 245), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cfe) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f99 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 222), (7, 243), (8, 247), (9, 191), (10, 101), (11, 245), (12, 131), (13, 93), (14, 216), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108d01) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108bc1_5 code

theorem rest_l108bc1_3 [Bindings] (code : CodeMap) :
    Rest (n := 173) code lifted (codeRange 0x108bc1 bytes_l108bc1) [(0, 159), (1, 171), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]
      111 0x108c74 bytes_l108bc1_3 b_l108bc1_3 := by
  have f60 : InstrSpec 0x108c74 [0x48, 0x09, 0xF1] (fun s => s.RIP = 0x108c74) (orR64R64Effect 0x108c74 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108c74 1 6).toInstrSpec (or_r64_r64_effect_step 0x108c74 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x108c77 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x108c77) (shrR64Effect 0x108c77 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x108c77 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x108c77 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x108c7b [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x108c7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108c7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108c7b 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108c7b 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108c7b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f63 : InstrSpec 0x108c80 [0x48, 0x8D, 0x4C, 0x24, 0x10] (fun s => s.RIP = 0x108c80) (leaR64Effect 0x108c80 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x108c80 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x108c80 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x108c85 [0x45, 0x31, 0xC9] (fun s => s.RIP = 0x108c85) (xorR32R32Effect 0x108c85 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x108c85 3 9 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x108c85 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x108c88 [0x4C, 0x2B, 0x4C, 0x24, 0x10] (LoadPre 0x108c88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108c88 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108c88 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (subR64M64Effect_footprint 0x108c88 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (sub_r64_m64_effect_step 0x108c88 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x108c8d [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x108c8d) (movR64R64Effect 0x108c8d 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x108c8d 6 3).toInstrSpec (mov_r64_r64_effect_step 0x108c8d 0x48 0xde (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x108c90 [0x4C, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x108c90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x108c90 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108c90 8 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x108c90 8 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x108c90 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f68 : InstrSpec 0x108c95 [0x4C, 0x29, 0xC6] (fun s => s.RIP = 0x108c95) (subR64R64Effect 0x108c95 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108c95 6 8).toInstrSpec (sub_r64_r64_effect_step 0x108c95 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x108c98 [0x49, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x108c98) (sarR64Effect 0x108c98 4 9 63)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (sarR64Effect_footprint 0x108c98 4 9 63).toInstrSpec (sar_r64_imm8_effect_step 0x108c98 0x49 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x108c9c [0x49, 0x01, 0xF1] (fun s => s.RIP = 0x108c9c) (addR64R64Effect 0x108c9c 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108c9c 9 6).toInstrSpec (add_r64_r64_effect_step 0x108c9c 0x49 0xf1 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x108c9f [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x108c9f) (movR64R64Effect 0x108c9f 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x108c9f 6 3).toInstrSpec (mov_r64_r64_effect_step 0x108c9f 0x48 0xde (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x108ca2 [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x108ca2) (notR64Effect 0x108ca2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x108ca2 6).toInstrSpec (not_r64_effect_step 0x108ca2 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x108ca5 [0x4C, 0x89, 0xC7] (fun s => s.RIP = 0x108ca5) (movR64R64Effect 0x108ca5 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x108ca5 7 8).toInstrSpec (mov_r64_r64_effect_step 0x108ca5 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x108ca8 [0x48, 0x21, 0xF7] (fun s => s.RIP = 0x108ca8) (andR64R64Effect 0x108ca8 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108ca8 7 6).toInstrSpec (and_r64_r64_effect_step 0x108ca8 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x108cab [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x108cab) (orR64R64Effect 0x108cab 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108cab 6 8).toInstrSpec (or_r64_r64_effect_step 0x108cab 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x108cae [0x4C, 0x21, 0xCE] (fun s => s.RIP = 0x108cae) (andR64R64Effect 0x108cae 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108cae 6 9).toInstrSpec (and_r64_r64_effect_step 0x108cae 0x4c 0xce (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x108cb1 [0x48, 0x09, 0xFE] (fun s => s.RIP = 0x108cb1) (orR64R64Effect 0x108cb1 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108cb1 6 7).toInstrSpec (or_r64_r64_effect_step 0x108cb1 0x48 0xfe (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x108cb4 [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x108cb4) (shrR64Effect 0x108cb4 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x108cb4 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x108cb4 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x108cb8 [0x48, 0x89, 0x74, 0x24, 0x10] (StorePre 0x108cb8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cb8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108cb8 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x108cb8 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108cb8 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f60 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 159), (1, 173), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c77) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f61 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 159), (1, 175), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c7b) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.exec (n := 177) (ρ' := [(0, 159), (1, 175), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c80) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 178) (RestInside.exec (n := 178) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c85) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f64 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 179), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c88) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f65 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 181), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c8d) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f66 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 183), (7, 157), (8, 85), (9, 181), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c90) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f67 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 183), (7, 157), (8, 185), (9, 181), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c95) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f68 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 187), (7, 157), (8, 185), (9, 181), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c98) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f69 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 187), (7, 157), (8, 185), (9, 189), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c9c) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f70 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 187), (7, 157), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c9f) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f71 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 193), (7, 157), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ca2) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f72 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 195), (7, 157), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ca5) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f73 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 195), (7, 197), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108ca8) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f74 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 195), (7, 199), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cab) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f75 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 201), (7, 199), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cae) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f76 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 203), (7, 199), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cb1) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f77 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 205), (7, 199), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cb4) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f78 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 207), (7, 199), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cb8) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.exec (n := 209) (ρ' := [(0, 159), (2, 153), (3, 151), (4, 4), (5, 111), (6, 207), (7, 199), (8, 185), (9, 191), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108cbd) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l108bc1_4 code

theorem rest_l108bc1_2 [Bindings] (code : CodeMap) :
    Rest (n := 133) code lifted (codeRange 0x108bc1 bytes_l108bc1) [(0, 95), (1, 123), (2, 129), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]
      131 0x108c3a bytes_l108bc1_2 b_l108bc1_2 := by
  have f40 : InstrSpec 0x108c3a [0x89, 0xC1] (fun s => s.RIP = 0x108c3a) (movR32R32Effect 0x108c3a 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108c3a 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x108c3a 0xc1 (by decide)) pre_rip
  have f41 : InstrSpec 0x108c3c [0x49, 0xD3, 0xE6] (fun s => s.RIP = 0x108c3c) (shlR64ClEffect 0x108c3c 3 14)
      [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x108c3c 3 14).toInstrSpec (shl_r64_cl_effect_step 0x108c3c 0x49 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x108c3f [0x4C, 0x89, 0xFB] (fun s => s.RIP = 0x108c3f) (movR64R64Effect 0x108c3f 3 15)
      [.gpr 15] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x108c3f 3 15).toInstrSpec (mov_r64_r64_effect_step 0x108c3f 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x108c42 [0x89, 0xE9] (fun s => s.RIP = 0x108c42) (movR32R32Effect 0x108c42 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108c42 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x108c42 0xe9 (by decide)) pre_rip
  have f44 : InstrSpec 0x108c44 [0x48, 0xD3, 0xEB] (fun s => s.RIP = 0x108c44) (shrR64ClEffect 0x108c44 3 3)
      [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x108c44 3 3).toInstrSpec (shr_r64_cl_effect_step 0x108c44 0x48 0xeb (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x108c47 [0x89, 0xC1] (fun s => s.RIP = 0x108c47) (movR32R32Effect 0x108c47 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108c47 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x108c47 0xc1 (by decide)) pre_rip
  have f46 : InstrSpec 0x108c49 [0x49, 0xD3, 0xE7] (fun s => s.RIP = 0x108c49) (shlR64ClEffect 0x108c49 3 15)
      [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x108c49 3 15).toInstrSpec (shl_r64_cl_effect_step 0x108c49 0x49 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x108c4c [0x89, 0xE9] (fun s => s.RIP = 0x108c4c) (movR32R32Effect 0x108c4c 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108c4c 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x108c4c 0xe9 (by decide)) pre_rip
  have f48 : InstrSpec 0x108c4e [0x48, 0xD3, 0xEA] (fun s => s.RIP = 0x108c4e) (shrR64ClEffect 0x108c4e 3 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x108c4e 3 2).toInstrSpec (shr_r64_cl_effect_step 0x108c4e 0x48 0xea (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x108c51 [0x4C, 0x09, 0xF3] (fun s => s.RIP = 0x108c51) (orR64R64Effect 0x108c51 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108c51 3 14).toInstrSpec (or_r64_r64_effect_step 0x108c51 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x108c54 [0x4C, 0x09, 0xFA] (fun s => s.RIP = 0x108c54) (orR64R64Effect 0x108c54 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108c54 2 15).toInstrSpec (or_r64_r64_effect_step 0x108c54 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x108c57 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x108c57) (movR64R64Effect 0x108c57 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x108c57 0 2).toInstrSpec (mov_r64_r64_effect_step 0x108c57 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x108c5a [0x48, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x108c5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x108c5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108c5a 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x108c5a 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x108c5a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x108c5f [0x48, 0x29, 0xF8] (fun s => s.RIP = 0x108c5f) (subR64R64Effect 0x108c5f 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x108c5f 0 7).toInstrSpec (sub_r64_r64_effect_step 0x108c5f 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x108c62 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x108c62) (movR64R64Effect 0x108c62 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x108c62 1 2).toInstrSpec (mov_r64_r64_effect_step 0x108c62 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x108c65 [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x108c65) (notR64Effect 0x108c65 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x108c65 1).toInstrSpec (not_r64_effect_step 0x108c65 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x108c68 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x108c68) (movR64R64Effect 0x108c68 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x108c68 6 7).toInstrSpec (mov_r64_r64_effect_step 0x108c68 0x48 0xfe (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x108c6b [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x108c6b) (andR64R64Effect 0x108c6b 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108c6b 6 1).toInstrSpec (and_r64_r64_effect_step 0x108c6b 0x48 0xce (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x108c6e [0x48, 0x09, 0xF9] (fun s => s.RIP = 0x108c6e) (orR64R64Effect 0x108c6e 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108c6e 1 7).toInstrSpec (or_r64_r64_effect_step 0x108c6e 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x108c71 [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x108c71) (andR64R64Effect 0x108c71 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108c71 1 0).toInstrSpec (and_r64_r64_effect_step 0x108c71 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 95), (1, 133), (2, 129), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c3c) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f41 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 95), (1, 133), (2, 129), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c3f) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f42 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 95), (1, 133), (2, 129), (3, 137), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c42) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 95), (1, 139), (2, 129), (3, 137), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c44) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f44 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 95), (1, 139), (2, 129), (3, 141), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c47) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 95), (1, 143), (2, 129), (3, 141), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c49) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f46 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 95), (1, 143), (2, 129), (3, 141), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c4c) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f47 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 95), (1, 147), (2, 129), (3, 141), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c4e) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 95), (1, 147), (2, 149), (3, 141), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c51) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f49 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 95), (1, 147), (2, 149), (3, 151), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c54) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 95), (1, 147), (2, 153), (3, 151), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c57) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f51 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 155), (1, 147), (2, 153), (3, 151), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c5a) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f52 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 155), (1, 147), (2, 153), (3, 151), (4, 4), (5, 111), (6, 103), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c5f) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 159), (1, 147), (2, 153), (3, 151), (4, 4), (5, 111), (6, 103), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c62) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f54 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 159), (1, 161), (2, 153), (3, 151), (4, 4), (5, 111), (6, 103), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c65) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f55 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 159), (1, 163), (2, 153), (3, 151), (4, 4), (5, 111), (6, 103), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c68) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f56 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 159), (1, 163), (2, 153), (3, 151), (4, 4), (5, 111), (6, 165), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c6b) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f57 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 159), (1, 163), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c6e) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 159), (1, 169), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c71) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 159), (1, 171), (2, 153), (3, 151), (4, 4), (5, 111), (6, 167), (7, 157), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 135), (15, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c74) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108bc1_3 code

theorem rest_l108bc1_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x108bc1 bytes_l108bc1) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 53), (11, 11), (12, 12), (13, 91), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]
      151 0x108c00 bytes_l108bc1_1 b_l108bc1_1 := by
  have f20 : InstrSpec 0x108c00 [0x49, 0x31, 0xC5] (fun s => s.RIP = 0x108c00) (xorR64R64Effect 0x108c00 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108c00 13 0).toInstrSpec (xor_r64_r64_effect_step 0x108c00 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x108c03 [0x89, 0xC8] (fun s => s.RIP = 0x108c03) (movR32R32Effect 0x108c03 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x108c03 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x108c03 0xc8 (by decide)) pre_rip
  have f22 : InstrSpec 0x108c05 [0x4D, 0x89, 0xEA] (fun s => s.RIP = 0x108c05) (movR64R64Effect 0x108c05 10 13)
      [.gpr 13] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x108c05 10 13).toInstrSpec (mov_r64_r64_effect_step 0x108c05 0x4d 0xea (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x108c08 [0x89, 0xC1] (fun s => s.RIP = 0x108c08) (movR32R32Effect 0x108c08 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108c08 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x108c08 0xc1 (by decide)) pre_rip
  have f24 : InstrSpec 0x108c0a [0x49, 0xD3, 0xE2] (fun s => s.RIP = 0x108c0a) (shlR64ClEffect 0x108c0a 3 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x108c0a 3 10).toInstrSpec (shl_r64_cl_effect_step 0x108c0a 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x108c0d [0x48, 0x8B, 0x74, 0x24, 0x48] (LoadPre 0x108c0d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108c0d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108c0d 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x108c0d 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x108c0d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x108c12 [0x48, 0x31, 0xF3] (fun s => s.RIP = 0x108c12) (xorR64R64Effect 0x108c12 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108c12 3 6).toInstrSpec (xor_r64_r64_effect_step 0x108c12 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x108c15 [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x108c15) (negR64Effect 0x108c15 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x108c15 2).toInstrSpec (neg_r64_effect_step 0x108c15 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x108c18 [0x49, 0x89, 0xFB] (fun s => s.RIP = 0x108c18) (movR64R64Effect 0x108c18 11 7)
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x108c18 11 7).toInstrSpec (mov_r64_r64_effect_step 0x108c18 0x49 0xfb (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x108c1b [0x8B, 0x6C, 0x24, 0x44] (LoadPre 0x108c1b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x108c1b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x108c1b 5 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x108c1b 5 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x108c1b 5 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x108c1f [0x89, 0xE9] (fun s => s.RIP = 0x108c1f) (movR32R32Effect 0x108c1f 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108c1f 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x108c1f 0xe9 (by decide)) pre_rip
  have f31 : InstrSpec 0x108c21 [0x49, 0xD3, 0xEB] (fun s => s.RIP = 0x108c21) (shrR64ClEffect 0x108c21 3 11)
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x108c21 3 11).toInstrSpec (shr_r64_cl_effect_step 0x108c21 0x49 0xeb (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x108c24 [0x89, 0xC1] (fun s => s.RIP = 0x108c24) (movR32R32Effect 0x108c24 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108c24 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x108c24 0xc1 (by decide)) pre_rip
  have f33 : InstrSpec 0x108c26 [0x48, 0xD3, 0xE7] (fun s => s.RIP = 0x108c26) (shlR64ClEffect 0x108c26 3 7)
      [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x108c26 3 7).toInstrSpec (shl_r64_cl_effect_step 0x108c26 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x108c29 [0x4D, 0x89, 0xF4] (fun s => s.RIP = 0x108c29) (movR64R64Effect 0x108c29 12 14)
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x108c29 12 14).toInstrSpec (mov_r64_r64_effect_step 0x108c29 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x108c2c [0x89, 0xE9] (fun s => s.RIP = 0x108c2c) (movR32R32Effect 0x108c2c 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108c2c 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x108c2c 0xe9 (by decide)) pre_rip
  have f36 : InstrSpec 0x108c2e [0x49, 0xD3, 0xEC] (fun s => s.RIP = 0x108c2e) (shrR64ClEffect 0x108c2e 3 12)
      [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x108c2e 3 12).toInstrSpec (shr_r64_cl_effect_step 0x108c2e 0x49 0xec (by decide) (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x108c31 [0x48, 0x21, 0xDA] (fun s => s.RIP = 0x108c31) (andR64R64Effect 0x108c31 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108c31 2 3).toInstrSpec (and_r64_r64_effect_step 0x108c31 0x48 0xda (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x108c34 [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x108c34) (xorR64R64Effect 0x108c34 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108c34 2 6).toInstrSpec (xor_r64_r64_effect_step 0x108c34 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x108c37 [0x49, 0x09, 0xFC] (fun s => s.RIP = 0x108c37) (orR64R64Effect 0x108c37 12 7)
      [.gpr 12, .gpr 7] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108c37 12 7).toInstrSpec (or_r64_r64_effect_step 0x108c37 0x49 0xfc (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 53), (11, 11), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c03) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 53), (11, 11), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c05) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 97), (11, 11), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c08) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 99), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 97), (11, 11), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c0a) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 95), (1, 99), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 101), (11, 11), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c0d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 95), (1, 99), (2, 2), (3, 3), (4, 4), (5, 61), (6, 103), (7, 59), (8, 85), (9, 9), (10, 101), (11, 11), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c12) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 95), (1, 99), (2, 2), (3, 105), (4, 4), (5, 61), (6, 103), (7, 59), (8, 85), (9, 9), (10, 101), (11, 11), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c15) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 95), (1, 99), (2, 107), (3, 105), (4, 4), (5, 61), (6, 103), (7, 59), (8, 85), (9, 9), (10, 101), (11, 11), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c18) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 95), (1, 99), (2, 107), (3, 105), (4, 4), (5, 61), (6, 103), (7, 59), (8, 85), (9, 9), (10, 101), (11, 109), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c1b) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 95), (1, 99), (2, 107), (3, 105), (4, 4), (5, 111), (6, 103), (7, 59), (8, 85), (9, 9), (10, 101), (11, 109), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c1f) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 95), (1, 113), (2, 107), (3, 105), (4, 4), (5, 111), (6, 103), (7, 59), (8, 85), (9, 9), (10, 101), (11, 109), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c21) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 95), (1, 113), (2, 107), (3, 105), (4, 4), (5, 111), (6, 103), (7, 59), (8, 85), (9, 9), (10, 101), (11, 115), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c24) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 95), (1, 117), (2, 107), (3, 105), (4, 4), (5, 111), (6, 103), (7, 59), (8, 85), (9, 9), (10, 101), (11, 115), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c26) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 95), (1, 117), (2, 107), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 12), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c29) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 95), (1, 117), (2, 107), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 121), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c2c) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 95), (1, 123), (2, 107), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 121), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c2e) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f36 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 95), (1, 123), (2, 107), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 125), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c31) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 95), (1, 123), (2, 127), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 125), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c34) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 95), (1, 123), (2, 129), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 125), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c37) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f39 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 95), (1, 123), (2, 129), (3, 105), (4, 4), (5, 111), (6, 103), (7, 119), (8, 85), (9, 9), (10, 101), (11, 115), (12, 131), (13, 93), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c3a) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108bc1_2 code

theorem rest_l108bc1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108bc1 bytes_l108bc1) (entryMap (live .l108bc1))
      171 0x108bc1 bytes_l108bc1 b_l108bc1 := by
  have f0 : InstrSpec 0x108bc1 [0x4D, 0x31, 0xEA] (fun s => s.RIP = 0x108bc1) (xorR64R64Effect 0x108bc1 10 13)
      [.gpr 10, .gpr 13] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108bc1 10 13).toInstrSpec (xor_r64_r64_effect_step 0x108bc1 0x4d 0xea (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x108bc4 [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x108bc4) (negR64Effect 0x108bc4 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x108bc4 7).toInstrSpec (neg_r64_effect_step 0x108bc4 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x108bc7 [0x4C, 0x21, 0xD7] (fun s => s.RIP = 0x108bc7) (andR64R64Effect 0x108bc7 7 10)
      [.gpr 7, .gpr 10] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108bc7 7 10).toInstrSpec (and_r64_r64_effect_step 0x108bc7 0x4c 0xd7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x108bca [0x4C, 0x31, 0xEF] (fun s => s.RIP = 0x108bca) (xorR64R64Effect 0x108bca 7 13)
      [.gpr 7, .gpr 13] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108bca 7 13).toInstrSpec (xor_r64_r64_effect_step 0x108bca 0x4c 0xef (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x108bcd [0x4C, 0x31, 0xDD] (fun s => s.RIP = 0x108bcd) (xorR64R64Effect 0x108bcd 5 11)
      [.gpr 5, .gpr 11] [] [.reg 5, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108bcd 5 11).toInstrSpec (xor_r64_r64_effect_step 0x108bcd 0x4c 0xdd (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x108bd0 [0x49, 0xF7, 0xDE] (fun s => s.RIP = 0x108bd0) (negR64Effect 0x108bd0 14)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (negR64Effect_footprint 0x108bd0 14).toInstrSpec (neg_r64_effect_step 0x108bd0 0x49 0xde (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x108bd3 [0x49, 0x21, 0xEE] (fun s => s.RIP = 0x108bd3) (andR64R64Effect 0x108bd3 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108bd3 14 5).toInstrSpec (and_r64_r64_effect_step 0x108bd3 0x49 0xee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x108bd6 [0x4D, 0x31, 0xDE] (fun s => s.RIP = 0x108bd6) (xorR64R64Effect 0x108bd6 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108bd6 14 11).toInstrSpec (xor_r64_r64_effect_step 0x108bd6 0x4d 0xde (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x108bd9 [0x4D, 0x31, 0xE0] (fun s => s.RIP = 0x108bd9) (xorR64R64Effect 0x108bd9 8 12)
      [.gpr 8, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108bd9 8 12).toInstrSpec (xor_r64_r64_effect_step 0x108bd9 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x108bdc [0x49, 0xF7, 0xDF] (fun s => s.RIP = 0x108bdc) (negR64Effect 0x108bdc 15)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (negR64Effect_footprint 0x108bdc 15).toInstrSpec (neg_r64_effect_step 0x108bdc 0x49 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x108bdf [0x4D, 0x21, 0xC7] (fun s => s.RIP = 0x108bdf) (andR64R64Effect 0x108bdf 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108bdf 15 8).toInstrSpec (and_r64_r64_effect_step 0x108bdf 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x108be2 [0x4D, 0x31, 0xE7] (fun s => s.RIP = 0x108be2) (xorR64R64Effect 0x108be2 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108be2 15 12).toInstrSpec (xor_r64_r64_effect_step 0x108be2 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x108be5 [0x83, 0xE6, 0x01] (fun s => s.RIP = 0x108be5) (andR32Imm8Effect 0x108be5 3 6 0x1)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x108be5 3 6 0x1).toInstrSpec (and_r32_imm8_effect_step 0x108be5 0xe6 0x1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x108be8 [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x108be8) (movR64R64Effect 0x108be8 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x108be8 8 0).toInstrSpec (mov_r64_r64_effect_step 0x108be8 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x108beb [0x49, 0xF7, 0xD0] (fun s => s.RIP = 0x108beb) (notR64Effect 0x108beb 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR64Effect_footprint 0x108beb 8).toInstrSpec (not_r64_effect_step 0x108beb 0x49 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x108bee [0x49, 0x01, 0xF0] (fun s => s.RIP = 0x108bee) (addR64R64Effect 0x108bee 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x108bee 8 6).toInstrSpec (add_r64_r64_effect_step 0x108bee 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x108bf1 [0x49, 0x31, 0xC0] (fun s => s.RIP = 0x108bf1) (xorR64R64Effect 0x108bf1 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x108bf1 8 0).toInstrSpec (xor_r64_r64_effect_step 0x108bf1 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x108bf4 [0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x10] (LoadPre 0x108bf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108bf4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108bf4 6 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x108bf4 6 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x108bf4 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x108bfa [0x49, 0xF7, 0xDD] (fun s => s.RIP = 0x108bfa) (negR64Effect 0x108bfa 13)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (negR64Effect_footprint 0x108bfa 13).toInstrSpec (neg_r64_effect_step 0x108bfa 0x49 0xdd (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x108bfd [0x4D, 0x21, 0xC5] (fun s => s.RIP = 0x108bfd) (andR64R64Effect 0x108bfd 13 8)
      [.gpr 13, .gpr 8] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x108bfd 13 8).toInstrSpec (and_r64_r64_effect_step 0x108bfd 0x4d 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bc4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bc7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bca) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bcd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bd0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bd3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bd6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bd9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bdc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bdf) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108be2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 6), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108be5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 69), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108be8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 79), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108beb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 81), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bee) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 83), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bf1) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bf4) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 53), (11, 11), (12, 12), (13, 87), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bfa) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 53), (11, 11), (12, 12), (13, 89), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108bfd) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 61), (6, 77), (7, 59), (8, 85), (9, 9), (10, 53), (11, 11), (12, 12), (13, 91), (14, 67), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108c00) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l108bc1_1 code

theorem block_l108bc1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108bc1 :=
  Rest.liftedBlock (rest_l108bc1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108bc1 x hx)

theorem rest_l108df9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108df9 bytes_l108df9) (entryMap (live .l108df9))
      4 0x108df9 bytes_l108df9 b_l108df9 := by
  have f0 : InstrSpec 0x108df9 [0xBE, 0x1B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108df9) (movR32Imm32Effect 0x108df9 5 6 0x1b)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x108df9 5 6 0x1b).toInstrSpec (mov_r32_imm32_effect_step 0x108df9 0xbe (by decide) 0x1b) pre_rip
  have f1 : InstrSpec 0x108dfe [0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x108dfe) (movR64Imm32Effect 0x108dfe 7 0x202b38)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x108dfe 7 0x202b38).toInstrSpec (mov_r64_imm32_effect_step 0x108dfe 0x48 0xc7 (by decide) (by decide) (by decide) 0x202b38) pre_rip
  have f2 : InstrSpec 0x108e05 [0x48, 0xC7, 0xC2, 0x58, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x108e05) (movR64Imm32Effect 0x108e05 2 0x202b58)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x108e05 2 0x202b58).toInstrSpec (mov_r64_imm32_effect_step 0x108e05 0x48 0xc2 (by decide) (by decide) (by decide) 0x202b58) pre_rip
  have f3 : InstrSpec 0x108e0c [0xE8, 0x4F, 0x07, 0x02, 0x00] (PushPre 0x108e0c 5) (callEffect (fun _ => 0x129560) 0x108e11)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x108e0c 0x129560 0x108e11).toInstrSpec (call_rel32_effect_step 0x108e0c 0x2074f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x108dfe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x108e05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x108e0c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129560) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l108df9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108df9 :=
  Rest.liftedBlock (rest_l108df9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108df9 x hx)

theorem rest_l108e11 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108e11 bytes_l108e11) (entryMap (live .l108e11))
      4 0x108e11 bytes_l108e11 b_l108e11 := by
  have f0 : InstrSpec 0x108e11 [0xBF, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108e11) (movR32Imm32Effect 0x108e11 5 7 0x4)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x108e11 5 7 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x108e11 0xbf (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x108e16 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108e16) (movR32Imm32Effect 0x108e16 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x108e16 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x108e16 0xbe (by decide) 0x4) pre_rip
  have f2 : InstrSpec 0x108e1b [0x48, 0xC7, 0xC2, 0x20, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x108e1b) (movR64Imm32Effect 0x108e1b 2 0x202b20)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x108e1b 2 0x202b20).toInstrSpec (mov_r64_imm32_effect_step 0x108e1b 0x48 0xc2 (by decide) (by decide) (by decide) 0x202b20) pre_rip
  have f3 : InstrSpec 0x108e22 [0xE8, 0xCB, 0x07, 0x02, 0x00] (PushPre 0x108e22 5) (callEffect (fun _ => 0x1295f2) 0x108e27)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x108e22 0x1295f2 0x108e27).toInstrSpec (call_rel32_effect_step 0x108e22 0x207cb (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x108e16) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x108e1b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x108e22) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x1295f2) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l108e11 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108e11 :=
  Rest.liftedBlock (rest_l108e11 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108e11 x hx)

theorem rest_l108e27 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108e27 bytes_l108e27) (entryMap (live .l108e27))
      1 0x108e27 bytes_l108e27 b_l108e27 := by
  have f0 : InstrSpec 0x108e27 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108e27) (fun _ => nopEffect 0x108e27 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x108e27 9).toInstrSpec (nop_m_effect_step 0x108e27 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108e30) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l108e27 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108e27 :=
  Rest.liftedBlock (rest_l108e27 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108e27 x hx)

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

theorem_by block_l108980_eval :
    program.runBlock (dialect code) ⟨.l108980, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10899e_eval :
    program.runBlock (dialect code) ⟨.l10899e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1089b2_eval :
    program.runBlock (dialect code) ⟨.l1089b2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108bb1_eval :
    program.runBlock (dialect code) ⟨.l108bb1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108bc1_eval :
    program.runBlock (dialect code) ⟨.l108bc1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108df9_eval :
    program.runBlock (dialect code) ⟨.l108df9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108e11_eval :
    program.runBlock (dialect code) ⟨.l108e11, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108e27_eval :
    program.runBlock (dialect code) ⟨.l108e27, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
