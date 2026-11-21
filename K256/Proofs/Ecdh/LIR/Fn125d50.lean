import K256.Proofs.Ecdh.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem rest_l125d50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125d50 bytes_l125d50) (entryMap (live .l125d50))
      13 0x125d50 bytes_l125d50 b_l125d50 := by
  have f0 : InstrSpec 0x125d50 [0x55] (PushPre 0x125d50 1) (pushR64Effect 0x125d50 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125d50 1 5).toInstrSpec (push_r64_effect_step 0x125d50 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x125d51 [0x41, 0x57] (PushPre 0x125d51 2) (pushR64Effect 0x125d51 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125d51 2 15).toInstrSpec (push_r64_rex_effect_step 0x125d51 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x125d53 [0x41, 0x56] (PushPre 0x125d53 2) (pushR64Effect 0x125d53 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125d53 2 14).toInstrSpec (push_r64_rex_effect_step 0x125d53 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x125d55 [0x41, 0x55] (PushPre 0x125d55 2) (pushR64Effect 0x125d55 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125d55 2 13).toInstrSpec (push_r64_rex_effect_step 0x125d55 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x125d57 [0x41, 0x54] (PushPre 0x125d57 2) (pushR64Effect 0x125d57 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125d57 2 12).toInstrSpec (push_r64_rex_effect_step 0x125d57 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x125d59 [0x53] (PushPre 0x125d59 1) (pushR64Effect 0x125d59 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125d59 1 3).toInstrSpec (push_r64_effect_step 0x125d59 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x125d5a [0x48, 0x81, 0xEC, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125d5a) (subR64Imm32Effect 0x125d5a 4 0xd8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x125d5a 4 0xd8).toInstrSpec (sub_r64_imm32_effect_step 0x125d5a 0x48 0xec 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x125d61 [0x89, 0xD1] (fun s => s.RIP = 0x125d61) (movR32R32Effect 0x125d61 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x125d61 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x125d61 0xd1 (by decide)) pre_rip
  have f8 : InstrSpec 0x125d63 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x125d63) (movR64R64Effect 0x125d63 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x125d63 14 6).toInstrSpec (mov_r64_r64_effect_step 0x125d63 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x125d66 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x125d66) (movR64R64Effect 0x125d66 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x125d66 3 7).toInstrSpec (mov_r64_r64_effect_step 0x125d66 0x48 0xfb (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x125d69 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x125d69) (leaR64Effect 0x125d69 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x125d69 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x125d69 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x125d6e [0xBA, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125d6e) (movR32Imm32Effect 0x125d6e 5 2 0x80)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x125d6e 5 2 0x80).toInstrSpec (mov_r32_imm32_effect_step 0x125d6e 0xba (by decide) 0x80) pre_rip
  have f12 : InstrSpec 0x125d73 [0xE8, 0x18, 0xE5, 0xFF, 0xFF] (PushPre 0x125d73 5) (callEffect (fun _ => 0x124290) 0x125d78)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x125d73 0x124290 0x125d78).toInstrSpec (call_rel32_effect_step 0x125d73 0xffffe518 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d51) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d53) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d55) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d57) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d59) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d5a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d61) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d63) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d66) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 67), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d69) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 67), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d6e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 67), (2, 75), (3, 71), (4, 65), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d73) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 67), (2, 75), (3, 71), (4, 77), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124290) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l125d50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125d50 :=
  Rest.liftedBlock (rest_l125d50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125d50 x hx)

theorem rest_l125d78 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125d78 bytes_l125d78) (entryMap (live .l125d78))
      4 0x125d78 bytes_l125d78 b_l125d78 := by
  have f0 : InstrSpec 0x125d78 [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x125d78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125d78 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125d78 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x125d78 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x125d78 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125d7c [0x0F, 0xB6, 0x44, 0x24, 0x0C] (LoadPre 0x125d7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125d7c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125d7c 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x125d7c 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x125d7c 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125d81 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x125d81) (cmpR32Imm8Effect 0x125d81 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x125d81 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x125d81 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d7c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d81) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d84) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x125d84 5 0xcb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125d78 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125d78 :=
  Rest.liftedBlock (rest_l125d78 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125d78 x hx)

theorem rest_l125d8a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125d8a bytes_l125d8a) (entryMap (live .l125d8a))
      2 0x125d8a bytes_l125d8a b_l125d8a := by
  have f0 : InstrSpec 0x125d8a [0xA8, 0x01] (fun s => s.RIP = 0x125d8a) (testAlImm8Effect 0x125d8a 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x125d8a 0x1).toInstrSpec (test_al_imm8_effect_step 0x125d8a 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d8c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x125d8c 4 0x10a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125d8a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125d8a :=
  Rest.liftedBlock (rest_l125d8a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125d8a x hx)

theorem rest_l125d92 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125d92 bytes_l125d92) (entryMap (live .l125d92))
      3 0x125d92 bytes_l125d92 b_l125d92 := by
  have f0 : InstrSpec 0x125d92 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x125d92) (leaR64Effect 0x125d92 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x125d92 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x125d92 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125d97 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x125d97) (movR64R64Effect 0x125d97 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x125d97 6 14).toInstrSpec (mov_r64_r64_effect_step 0x125d97 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x125d9a [0xE8, 0xB1, 0xF6, 0xFF, 0xFF] (PushPre 0x125d9a 5) (callEffect (fun _ => 0x125450) 0x125d9f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x125d9a 0x125450 0x125d9f).toInstrSpec (call_rel32_effect_step 0x125d9a 0xfffff6b1 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d97) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d9a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125450) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l125d92 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125d92 :=
  Rest.liftedBlock (rest_l125d92 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125d92 x hx)

theorem rest_l125d9f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125d9f bytes_l125d9f) (entryMap (live .l125d9f))
      3 0x125d9f bytes_l125d9f b_l125d9f := by
  have f0 : InstrSpec 0x125d9f [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x125d9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125d9f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125d9f 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x125d9f 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x125d9f 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125da3 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x125da3) (cmpR32Imm8Effect 0x125da3 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x125da3 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x125da3 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125da3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125da6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x125da6 5 0xff) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125d9f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125d9f :=
  Rest.liftedBlock (rest_l125d9f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125d9f x hx)

theorem rest_l125dac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125dac bytes_l125dac) (entryMap (live .l125dac))
      8 0x125dac bytes_l125dac b_l125dac := by
  have f0 : InstrSpec 0x125dac [0x44, 0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x125dac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125dac + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125dac 10 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x125dac 10 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x125dac 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125db1 [0x44, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x125db1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125db1 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125db1 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x125db1 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x125db1 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125db6 [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x125db6) (movR32R32Effect 0x125db6 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x125db6 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x125db6 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x125db9 [0x41, 0xC1, 0xEB, 0x08] (fun s => s.RIP = 0x125db9) (shrR32Effect 0x125db9 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x125db9 4 11 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x125db9 0x41 0xeb 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x125dbd [0x41, 0x0F, 0xB6, 0xC2] (fun s => s.RIP = 0x125dbd) (movzxR32R8Effect 0x125dbd 4 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x125dbd 4 0 10).toInstrSpec (movzx_r32_r8_rex_effect_step 0x125dbd 0x41 (by decide) 0xc2 (by decide)) pre_rip
  have f5 : InstrSpec 0x125dc1 [0x8D, 0x48, 0xEA] (fun s => s.RIP = 0x125dc1) (leaR32Effect 0x125dc1 3 1 (.base 0 (.d8 0xea)))
      [.gpr 0] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x125dc1 3 1 (.base 0 (.d8 0xea))).toInstrSpec (lea_r32_effect_step 0x125dc1 1 (.base 0 (.d8 0xea)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x125dc4 [0x83, 0xF9, 0x03] (fun s => s.RIP = 0x125dc4) (cmpR32Imm8Effect 0x125dc4 3 1 0x3)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x125dc4 3 1 0x3).toInstrSpec (cmp_r32_imm8_effect_step 0x125dc4 0xf9 0x3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125db1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125db6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 57), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125db9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 59), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125dbd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 59), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125dc1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 59), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125dc4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 59), (13, 13), (14, 14), (15, 55), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125dc7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel32_effect_step 0x125dc7 3 0x144) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125dac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125dac :=
  Rest.liftedBlock (rest_l125dac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125dac x hx)

theorem rest_l125dcd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125dcd bytes_l125dcd) (entryMap (live .l125dcd))
      2 0x125dcd bytes_l125dcd b_l125dcd := by
  have f0 : InstrSpec 0x125dcd [0x41, 0xF6, 0xC3, 0x01] (fun s => s.RIP = 0x125dcd) (testR8Imm8Effect 0x125dcd 11 0x1)
      [.gpr 11] [] [.flags, .rip] :=
    (testR8Imm8Effect_footprint 0x125dcd 11 0x1).toInstrSpec (test_r8_imm8_effect_step 0x125dcd 0x41 0xc3 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125dd1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x125dd1 4 0x177) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125dcd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125dcd :=
  Rest.liftedBlock (rest_l125dcd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125dcd x hx)

theorem rest_l125dd7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125dd7 bytes_l125dd7) (entryMap (live .l125dd7))
      2 0x125dd7 bytes_l125dd7 b_l125dd7 := by
  have f0 : InstrSpec 0x125dd7 [0x41, 0x80, 0xFA, 0x17] (fun s => s.RIP = 0x125dd7) (cmpR8Imm8Effect 0x125dd7 4 10 0x17)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x125dd7 4 10 0x17).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x125dd7 0x41 0xfa 0x17 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ddb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x125ddb 5 0x138) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125dd7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125dd7 :=
  Rest.liftedBlock (rest_l125dd7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125dd7 x hx)

theorem rest_l125de1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125de1 bytes_l125de1) (entryMap (live .l125de1))
      5 0x125de1 bytes_l125de1 b_l125de1 := by
  have f0 : InstrSpec 0x125de1 [0x49, 0xBD, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x125de1) (movR64Imm64Effect 0x125de1 13 0xffffffff00000000)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x125de1 13 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x125de1 0x49 0xbd (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f1 : InstrSpec 0x125deb [0x45, 0x8B, 0x66, 0x1C] (LoadPre 0x125deb (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125deb + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125deb 12 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x125deb 12 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x125deb 0x45 (by decide) 4 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125def [0x8B, 0x6C, 0x24, 0x14] (LoadPre 0x125def (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125def + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125def 5 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x125def 5 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x125def 5 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125df3 [0x44, 0x01, 0xE5] (fun s => s.RIP = 0x125df3) (addR32R32Effect 0x125df3 3 5 12)
      [.gpr 5, .gpr 12] [] [.reg 5, .flags, .rip] :=
    (addR32R32Effect_footprint 0x125df3 3 5 12).toInstrSpec (add_r32_r32_rex_effect_step 0x125df3 0x44 0xe5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125deb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125def) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125df3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125df6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel32_effect_step 0x125df6 2 0x4d5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125de1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125de1 :=
  Rest.liftedBlock (rest_l125de1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125de1 x hx)

theorem rest_l125dfc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125dfc bytes_l125dfc) (entryMap (live .l125dfc))
      7 0x125dfc bytes_l125dfc b_l125dfc := by
  have f0 : InstrSpec 0x125dfc [0x49, 0x8B, 0x36] (LoadPre 0x125dfc (fun s => AddrMode.addr (.base 14 .none) s (0x125dfc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x125dfc 6 (.base 14 .none))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125dfc 6 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x125dfc 0x49 (by decide) 6 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125dff [0x49, 0x8B, 0x56, 0x08] (LoadPre 0x125dff (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x125dff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x125dff 2 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125dff 2 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x125dff 0x49 (by decide) 2 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125e03 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x125e03) (leaR64Effect 0x125e03 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x125e03 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x125e03 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x125e08 [0x48, 0x89, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x125e08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x125e08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125e08 6 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e08 6 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x125e08 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125e10 [0x48, 0x89, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x125e10 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125e10 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125e10 2 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e10 2 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x125e10 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x125e18 [0x89, 0xE9] (fun s => s.RIP = 0x125e18) (movR32R32Effect 0x125e18 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x125e18 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x125e18 0xe9 (by decide)) pre_rip
  have f6 : InstrSpec 0x125e1a [0xE8, 0x31, 0x1E, 0x00, 0x00] (PushPre 0x125e1a 5) (callEffect (fun _ => 0x127c50) 0x125e1f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x125e1a 0x127c50 0x125e1f).toInstrSpec (call_rel32_effect_step 0x125e1a 0x1e31 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125dff) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e03) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e08) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e10) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e18) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e1a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 55), (3, 3), (4, 63), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c50) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l125dfc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125dfc :=
  Rest.liftedBlock (rest_l125dfc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125dfc x hx)

theorem rest_l125e1f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125e1f bytes_l125e1f) (entryMap (live .l125e1f))
      3 0x125e1f bytes_l125e1f b_l125e1f := by
  have f0 : InstrSpec 0x125e1f [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x125e1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125e1f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125e1f 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x125e1f 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x125e1f 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125e23 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x125e23) (cmpR32Imm8Effect 0x125e23 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x125e23 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x125e23 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e23) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e26) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x125e26 5 0x1dd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125e1f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125e1f :=
  Rest.liftedBlock (rest_l125e1f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125e1f x hx)

theorem rest_l125e2c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125e2c bytes_l125e2c) (entryMap (live .l125e2c))
      7 0x125e2c bytes_l125e2c b_l125e2c := by
  have f0 : InstrSpec 0x125e2c [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x125e2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125e2c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e2c 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x125e2c 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x125e2c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125e31 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x125e31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125e31 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e31 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x125e31 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x125e31 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125e36 [0x49, 0x89, 0x06] (StorePre 0x125e36 3 (fun s => AddrMode.addr (.base 14 .none) s (0x125e36 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x125e36 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e36 0 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x125e36 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x125e39 [0x49, 0x89, 0x4E, 0x08] (StorePre 0x125e39 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x125e39 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e39 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e39 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x125e39 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125e3d [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x125e3d (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x125e3d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x125e3d 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x125e3d 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x125e3d 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125e41 [0x48, 0x83, 0xF8, 0x3F] (fun s => s.RIP = 0x125e41) (cmpR64Imm8Effect 0x125e41 0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x125e41 0 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x125e41 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e36) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e39) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e3d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e41) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e45) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel32_effect_step 0x125e45 6 0x200) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125e2c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125e2c :=
  Rest.liftedBlock (rest_l125e2c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125e2c x hx)

theorem rest_l125e4b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125e4b bytes_l125e4b) (entryMap (live .l125e4b))
      2 0x125e4b bytes_l125e4b b_l125e4b := by
  have f0 : InstrSpec 0x125e4b [0xB9, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125e4b) (movR32Imm32Effect 0x125e4b 5 1 0x6)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x125e4b 5 1 0x6).toInstrSpec (mov_r32_imm32_effect_step 0x125e4b 0xb9 (by decide) 0x6) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e50) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x125e50 0x213 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125e4b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125e4b :=
  Rest.liftedBlock (rest_l125e4b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125e4b x hx)

theorem rest_l125e55 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125e55 bytes_l125e55) (entryMap (live .l125e55))
      17 0x125e55 bytes_l125e55 b_l125e55 := by
  have f0 : InstrSpec 0x125e55 [0x8B, 0x54, 0x24, 0x3C] (LoadPre 0x125e55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125e55 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125e55 2 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x125e55 2 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x125e55 2 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125e59 [0x89, 0x53, 0x34] (StorePre 0x125e59 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x125e59 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125e59 2 (.base 3 (.d8 0x34)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125e59 2 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x125e59 2 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x125e5c [0x48, 0x8B, 0x54, 0x24, 0x35] (LoadPre 0x125e5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x125e5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e5c 2 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125e5c 2 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (mov_r64_m64_effect_step 0x125e5c 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125e61 [0x48, 0x89, 0x53, 0x2D] (StorePre 0x125e61 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x125e61 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e61 2 (.base 3 (.d8 0x2d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e61 2 (.base 3 (.d8 0x2d))).toInstrSpec (mov_m64_r64_effect_step 0x125e61 0x48 (by decide) 2 (.base 3 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125e65 [0x48, 0x8B, 0x54, 0x24, 0x2D] (LoadPre 0x125e65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x125e65 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e65 2 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125e65 2 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (mov_r64_m64_effect_step 0x125e65 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125e6a [0x48, 0x89, 0x53, 0x25] (StorePre 0x125e6a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x125e6a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e6a 2 (.base 3 (.d8 0x25)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e6a 2 (.base 3 (.d8 0x25))).toInstrSpec (mov_m64_r64_effect_step 0x125e6a 0x48 (by decide) 2 (.base 3 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x125e6e [0x48, 0x8B, 0x54, 0x24, 0x25] (LoadPre 0x125e6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x125e6e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e6e 2 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125e6e 2 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (mov_r64_m64_effect_step 0x125e6e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x125e73 [0x48, 0x89, 0x53, 0x1D] (StorePre 0x125e73 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x125e73 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e73 2 (.base 3 (.d8 0x1d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e73 2 (.base 3 (.d8 0x1d))).toInstrSpec (mov_m64_r64_effect_step 0x125e73 0x48 (by decide) 2 (.base 3 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x125e77 [0x48, 0x8B, 0x54, 0x24, 0x1D] (LoadPre 0x125e77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x125e77 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e77 2 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125e77 2 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_r64_m64_effect_step 0x125e77 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x125e7c [0x48, 0x89, 0x53, 0x15] (StorePre 0x125e7c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x125e7c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e7c 2 (.base 3 (.d8 0x15)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e7c 2 (.base 3 (.d8 0x15))).toInstrSpec (mov_m64_r64_effect_step 0x125e7c 0x48 (by decide) 2 (.base 3 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x125e80 [0x48, 0x8B, 0x54, 0x24, 0x0D] (LoadPre 0x125e80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x125e80 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e80 2 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125e80 2 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_r64_m64_effect_step 0x125e80 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x125e85 [0x48, 0x8B, 0x74, 0x24, 0x15] (LoadPre 0x125e85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x125e85 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125e85 6 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125e85 6 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_r64_m64_effect_step 0x125e85 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x125e8a [0x48, 0x89, 0x73, 0x0D] (StorePre 0x125e8a 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x125e8a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e8a 6 (.base 3 (.d8 0xd)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e8a 6 (.base 3 (.d8 0xd))).toInstrSpec (mov_m64_r64_effect_step 0x125e8a 0x48 (by decide) 6 (.base 3 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x125e8e [0x48, 0x89, 0x53, 0x05] (StorePre 0x125e8e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x125e8e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125e8e 2 (.base 3 (.d8 0x5)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125e8e 2 (.base 3 (.d8 0x5))).toInstrSpec (mov_m64_r64_effect_step 0x125e8e 0x48 (by decide) 2 (.base 3 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125e92 [0x89, 0x0B] (StorePre 0x125e92 2 (fun s => AddrMode.addr (.base 3 .none) s (0x125e92 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x125e92 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125e92 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x125e92 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x125e94 [0x88, 0x43, 0x04] (StorePre 0x125e94 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x125e94 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x125e94 3 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x125e94 3 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x125e94 0 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e59) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e5c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e61) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e65) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e6a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e6e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e73) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e77) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e7c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e80) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e85) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e8a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e8e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e92) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e94) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125e97) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 76) (jmp_rel32_effect_step 0x125e97 0x158 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125e55 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125e55 :=
  Rest.liftedBlock (rest_l125e55 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125e55 x hx)

theorem rest_l125e9c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125e9c bytes_l125e9c) (entryMap (live .l125e9c))
      3 0x125e9c bytes_l125e9c b_l125e9c := by
  have f0 : InstrSpec 0x125e9c [0xC6, 0x43, 0x24, 0x02] (StorePre 0x125e9c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x125e9c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x125e9c (.base 3 (.d8 0x24)) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x125e9c (.base 3 (.d8 0x24)) 0x2).toInstrSpec (mov_m8_imm8_effect_step 0x125e9c (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x125ea0 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x125ea0 6 (fun s => AddrMode.addr (.base 3 .none) s (0x125ea0 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x125ea0 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x125ea0 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x125ea0 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ea0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ea6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x125ea6 0x149 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125e9c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125e9c :=
  Rest.liftedBlock (rest_l125e9c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125e9c x hx)

theorem rest_l125eab [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125eab bytes_l125eab) (entryMap (live .l125eab))
      20 0x125eab bytes_l125eab b_l125eab := by
  have f0 : InstrSpec 0x125eab [0x0F, 0xB6, 0x54, 0x24, 0x0C] (LoadPre 0x125eab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125eab + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125eab 5 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x125eab 5 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x125eab 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125eb0 [0x44, 0x0F, 0xB6, 0x74, 0x24, 0x0D] (LoadPre 0x125eb0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x125eb0 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125eb0 6 14 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x125eb0 6 14 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125eb0 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125eb6 [0x44, 0x0F, 0xB7, 0x64, 0x24, 0x0E] (LoadPre 0x125eb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x125eb6 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125eb6 6 12 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movzxR32M16Effect_footprint 0x125eb6 6 12 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x125eb6 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125ebc [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x125ebc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125ebc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125ebc 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x125ebc 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x125ebc 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x125ec1 [0x44, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x125ec1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125ec1 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125ec1 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x125ec1 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x125ec1 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125ec6 [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x1C] (LoadPre 0x125ec6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125ec6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125ec6 6 10 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x125ec6 6 10 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125ec6 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x125ecc [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x1D] (LoadPre 0x125ecc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x125ecc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125ecc 6 11 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x125ecc 6 11 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125ecc 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x125ed2 [0x44, 0x0F, 0xB7, 0x44, 0x24, 0x1E] (LoadPre 0x125ed2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x125ed2 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125ed2 6 8 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x125ed2 6 8 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x125ed2 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125ed8 [0x4C, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x125ed8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125ed8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125ed8 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125ed8 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x125ed8 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x125edd [0x49, 0xBD, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x125edd) (movR64Imm64Effect 0x125edd 13 0xffffffff00000000)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x125edd 13 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x125edd 0x49 0xbd (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f10 : InstrSpec 0x125ee7 [0x4D, 0x21, 0xCD] (fun s => s.RIP = 0x125ee7) (andR64R64Effect 0x125ee7 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x125ee7 13 9).toInstrSpec (and_r64_r64_effect_step 0x125ee7 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x125eea [0x8B, 0x74, 0x24, 0x28] (LoadPre 0x125eea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x125eea + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125eea 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x125eea 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x125eea 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x125eee [0x0F, 0xB6, 0x7C, 0x24, 0x2C] (LoadPre 0x125eee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125eee + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125eee 5 7 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x125eee 5 7 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (movzx_r32_m8_effect_step 0x125eee 7 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x125ef3 [0x48, 0x8B, 0x6C, 0x24, 0x2D] (LoadPre 0x125ef3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x125ef3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125ef3 5 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x125ef3 5 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (mov_r64_m64_effect_step 0x125ef3 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x125ef8 [0x48, 0x89, 0x6C, 0x24, 0x40] (StorePre 0x125ef8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125ef8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125ef8 5 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125ef8 5 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x125ef8 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x125efd [0x48, 0x8B, 0x6C, 0x24, 0x35] (LoadPre 0x125efd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x125efd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125efd 5 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x125efd 5 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (mov_r64_m64_effect_step 0x125efd 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x125f02 [0x48, 0x89, 0x6C, 0x24, 0x48] (StorePre 0x125f02 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x125f02 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125f02 5 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125f02 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x125f02 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x125f07 [0x8B, 0x6C, 0x24, 0x3C] (LoadPre 0x125f07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125f07 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125f07 5 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x125f07 5 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x125f07 5 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x125f0b [0x89, 0x6C, 0x24, 0x4F] (StorePre 0x125f0b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x125f0b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125f0b 5 (.sib 4 none 0 (.d8 0x4f)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125f0b 5 (.sib 4 none 0 (.d8 0x4f))).toInstrSpec (mov_m32_r32_low_effect_step 0x125f0b 5 (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125eb0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125eb6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (12, 57), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ebc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (12, 57), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ec1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (12, 57), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ec6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (10, 63), (12, 57), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ecc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (10, 63), (11, 65), (12, 57), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ed2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (8, 67), (10, 63), (11, 65), (12, 57), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ed8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125edd) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 71), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ee7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125eea) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (6, 75), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125eee) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (6, 75), (7, 77), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ef3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (5, 79), (6, 75), (7, 77), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ef8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (5, 79), (6, 75), (7, 77), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125efd) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (5, 82), (6, 75), (7, 77), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f02) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (5, 82), (6, 75), (7, 77), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f07) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (5, 85), (6, 75), (7, 77), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f0b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 59), (2, 53), (3, 3), (4, 4), (5, 85), (6, 75), (7, 77), (8, 67), (9, 69), (10, 63), (11, 65), (12, 57), (13, 73), (14, 55), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f0f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 88) (jmp_rel8_effect_step 0x125f0f 0x67 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125eab [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125eab :=
  Rest.liftedBlock (rest_l125eab code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125eab x hx)

theorem rest_l125f11 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125f11 bytes_l125f11) (entryMap (live .l125f11))
      3 0x125f11 bytes_l125f11 b_l125f11 := by
  have f0 : InstrSpec 0x125f11 [0x83, 0xC0, 0xF6] (fun s => s.RIP = 0x125f11) (addR32Imm8Effect 0x125f11 3 0 0xf6)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32Imm8Effect_footprint 0x125f11 3 0 0xf6).toInstrSpec (add_r32_imm8_effect_step 0x125f11 0xc0 0xf6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125f14 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x125f14) (cmpR32Imm8Effect 0x125f14 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x125f14 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x125f14 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f14) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f17) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x125f17 3 0x35) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125f11 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125f11 :=
  Rest.liftedBlock (rest_l125f11 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125f11 x hx)

theorem rest_l125f19 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125f19 bytes_l125f19) (entryMap (live .l125f19))
      13 0x125f19 bytes_l125f19 b_l125f19 := by
  have f0 : InstrSpec 0x125f19 [0x45, 0x89, 0xD0] (fun s => s.RIP = 0x125f19) (movR32R32Effect 0x125f19 3 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x125f19 3 8 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x125f19 0x45 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125f1c [0x41, 0xC1, 0xE8, 0x10] (fun s => s.RIP = 0x125f1c) (shrR32Effect 0x125f1c 4 8 16)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x125f1c 4 8 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x125f1c 0x41 0xe8 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x125f20 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x125f20 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x125f20 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x125f20 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x125f20 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x125f20 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x125f25 [0x41, 0x8B, 0x56, 0x1C] (LoadPre 0x125f25 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125f25 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125f25 2 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR32M32Effect_footprint 0x125f25 2 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x125f25 0x41 (by decide) 2 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x125f29 [0x41, 0x89, 0xD6] (fun s => s.RIP = 0x125f29) (movR32R32Effect 0x125f29 3 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x125f29 3 14 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x125f29 0x41 0xd6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x125f2c [0x41, 0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x125f2c) (shrR32Effect 0x125f2c 4 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR32Effect_footprint 0x125f2c 4 14 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x125f2c 0x41 0xee 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x125f30 [0x41, 0x89, 0xD4] (fun s => s.RIP = 0x125f30) (movR32R32Effect 0x125f30 3 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x125f30 3 12 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x125f30 0x41 0xd4 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x125f33 [0x41, 0xC1, 0xEC, 0x10] (fun s => s.RIP = 0x125f33) (shrR32Effect 0x125f33 4 12 16)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x125f33 4 12 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x125f33 0x41 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x125f37 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125f37) (movR32Imm32Effect 0x125f37 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x125f37 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x125f37 0xb8 (by decide) 0x1) pre_rip
  have f9 : InstrSpec 0x125f3c [0x48, 0xB9, 0x11, 0x00, 0x00, 0x00, 0xFF, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125f3c) (movR64Imm64Effect 0x125f3c 1 0xff00000011)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x125f3c 1 0xff00000011).toInstrSpec (mov_r64_imm64_effect_step 0x125f3c 0x48 0xb9 (by decide) (by decide) 0xff00000011) pre_rip
  have f10 : InstrSpec 0x125f46 [0x45, 0x31, 0xED] (fun s => s.RIP = 0x125f46) (xorR32R32Effect 0x125f46 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x125f46 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x125f46 0x45 0xed (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x125f49 [0x45, 0x89, 0xF9] (fun s => s.RIP = 0x125f49) (movR32R32Effect 0x125f49 3 9 15)
      [.gpr 15] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x125f49 3 9 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x125f49 0x45 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f1c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f20) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f25) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f29) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f2c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f30) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (12, 64), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f33) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (12, 66), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f37) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (12, 66), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f3c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (1, 70), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (12, 66), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f46) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 68), (1, 70), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (12, 66), (13, 72), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f49) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 68), (1, 70), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 74), (10, 10), (11, 11), (12, 66), (13, 72), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f4c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 76) (jmp_rel8_effect_step 0x125f4c 0x2a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125f19 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125f19 :=
  Rest.liftedBlock (rest_l125f19 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125f19 x hx)

theorem rest_l125f4e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125f4e bytes_l125f4e) (entryMap (live .l125f4e))
      11 0x125f4e bytes_l125f4e b_l125f4e := by
  have f0 : InstrSpec 0x125f4e [0x49, 0xC1, 0xE2, 0x20] (fun s => s.RIP = 0x125f4e) (shlR64Effect 0x125f4e 4 10 32)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64Effect_footprint 0x125f4e 4 10 32).toInstrSpec (shl_r64_imm8_effect_step 0x125f4e 0x49 0xe2 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125f52 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x125f52 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x125f52 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x125f52 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x125f52 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x125f52 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x125f57 [0x41, 0x8B, 0x56, 0x1C] (LoadPre 0x125f57 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125f57 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125f57 2 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR32M32Effect_footprint 0x125f57 2 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x125f57 0x41 (by decide) 2 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125f5b [0x41, 0x89, 0xD6] (fun s => s.RIP = 0x125f5b) (movR32R32Effect 0x125f5b 3 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x125f5b 3 14 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x125f5b 0x41 0xd6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x125f5e [0x41, 0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x125f5e) (shrR32Effect 0x125f5e 4 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR32Effect_footprint 0x125f5e 4 14 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x125f5e 0x41 0xee 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x125f62 [0x41, 0x89, 0xD4] (fun s => s.RIP = 0x125f62) (movR32R32Effect 0x125f62 3 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x125f62 3 12 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x125f62 0x41 0xd4 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x125f65 [0x41, 0xC1, 0xEC, 0x10] (fun s => s.RIP = 0x125f65) (shrR32Effect 0x125f65 4 12 16)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x125f65 4 12 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x125f65 0x41 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x125f69 [0x49, 0x83, 0xCA, 0x07] (fun s => s.RIP = 0x125f69) (orR64Imm8Effect 0x125f69 10 0x7)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x125f69 10 0x7).toInstrSpec (or_r64_imm8_effect_step 0x125f69 0x49 0xca 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x125f6d [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125f6d) (movR32Imm32Effect 0x125f6d 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x125f6d 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x125f6d 0xb8 (by decide) 0x1) pre_rip
  have f9 : InstrSpec 0x125f72 [0x45, 0x31, 0xED] (fun s => s.RIP = 0x125f72) (xorR32R32Effect 0x125f72 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x125f72 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x125f72 0x45 0xed (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x125f75 [0x4C, 0x89, 0xD1] (fun s => s.RIP = 0x125f75) (movR64R64Effect 0x125f75 1 10)
      [.gpr 10] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x125f75 1 10).toInstrSpec (mov_r64_r64_effect_step 0x125f75 0x4c 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f52) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f57) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f5b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f5e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f62) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 62), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f65) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 64), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f69) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 66), (11, 11), (12, 64), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f6d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 66), (11, 11), (12, 64), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f72) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 68), (2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 66), (11, 11), (12, 64), (13, 70), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f75) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 68), (1, 72), (2, 56), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 66), (11, 11), (12, 64), (13, 70), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f78) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l125f4e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125f4e :=
  Rest.liftedBlock (rest_l125f4e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125f4e x hx)

theorem rest_l125f78_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x125f78 bytes_l125f78) [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 89), (10, 83), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x125fbf bytes_l125f78_1 b_l125f78_1 := by
  have f20 : InstrSpec 0x125fbf [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x40] (LoadPre 0x125fbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125fbf + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125fbf 6 9 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x125fbf 6 9 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x125fbf 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x125fc5 [0x66, 0x44, 0x89, 0x4B, 0x25] (StorePre 0x125fc5 5 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x125fc5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x125fc5 5 9 (.base 3 (.d8 0x25)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x125fc5 5 9 (.base 3 (.d8 0x25))).toInstrSpec (mov_m16_r16_rex_effect_step 0x125fc5 0x44 (by decide) 1 (.base 3 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x125fca [0x4C, 0x8B, 0x4C, 0x24, 0x43] (LoadPre 0x125fca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x125fca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125fca 9 (.sib 4 none 0 (.d8 0x43)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125fca 9 (.sib 4 none 0 (.d8 0x43))).toInstrSpec (mov_r64_m64_effect_step 0x125fca 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x43)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x125fcf [0x4C, 0x8B, 0x5C, 0x24, 0x4B] (LoadPre 0x125fcf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x125fcf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125fcf 11 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x125fcf 11 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (mov_r64_m64_effect_step 0x125fcf 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x125fd4 [0x4C, 0x89, 0x4B, 0x28] (StorePre 0x125fd4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x125fd4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fd4 9 (.base 3 (.d8 0x28)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125fd4 9 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x125fd4 0x4c (by decide) 1 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x125fd8 [0x4C, 0x89, 0x5B, 0x30] (StorePre 0x125fd8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x125fd8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fd8 11 (.base 3 (.d8 0x30)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125fd8 11 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x125fd8 0x4c (by decide) 3 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x125fdc [0x89, 0x03] (StorePre 0x125fdc 2 (fun s => AddrMode.addr (.base 3 .none) s (0x125fdc + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x125fdc 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125fdc 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x125fdc 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x125fde [0x89, 0x53, 0x04] (StorePre 0x125fde 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x125fde + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125fde 2 (.base 3 (.d8 0x4)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125fde 2 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x125fde 2 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x125fe1 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x125fe1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125fe1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fe1 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125fe1 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x125fe1 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x125fe5 [0x4C, 0x89, 0x53, 0x10] (StorePre 0x125fe5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x125fe5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fe5 10 (.base 3 (.d8 0x10)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125fe5 10 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x125fe5 0x4c (by decide) 2 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x125fe9 [0x4C, 0x89, 0x43, 0x18] (StorePre 0x125fe9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x125fe9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125fe9 8 (.base 3 (.d8 0x18)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125fe9 8 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x125fe9 0x4c (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x125fed [0x89, 0x73, 0x20] (StorePre 0x125fed 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x125fed + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125fed 6 (.base 3 (.d8 0x20)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125fed 6 (.base 3 (.d8 0x20))).toInstrSpec (mov_m32_r32_low_effect_step 0x125fed 6 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x125ff0 [0x40, 0x88, 0x7B, 0x24] (StorePre 0x125ff0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x125ff0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125ff0 4 7 (.base 3 (.d8 0x24)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x125ff0 4 7 (.base 3 (.d8 0x24))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125ff0 0x40 (by decide) 7 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 92), (10, 83), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fc5) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 92), (10, 83), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fca) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fcf) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fd4) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fd8) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fdc) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fde) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fe1) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fe5) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fe9) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fed) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ff0) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 95), (10, 83), (11, 97), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ff4) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 108) (by decide) rfl

theorem rest_l125f78 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125f78 bytes_l125f78) (entryMap (live .l125f78))
      33 0x125f78 bytes_l125f78 b_l125f78 := by
  have f0 : InstrSpec 0x125f78 [0x41, 0xC1, 0xE4, 0x10] (fun s => s.RIP = 0x125f78) (shlR32Effect 0x125f78 4 12 16)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x125f78 4 12 16).toInstrSpec (shl_r32_imm8_rex_effect_step 0x125f78 0x41 0xe4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125f7c [0x41, 0x0F, 0xB6, 0xEE] (fun s => s.RIP = 0x125f7c) (movzxR32R8Effect 0x125f7c 4 5 14)
      [.gpr 14] [] [.reg 5, .rip] :=
    (movzxR32R8Effect_footprint 0x125f7c 4 5 14).toInstrSpec (movzx_r32_r8_rex_effect_step 0x125f7c 0x41 (by decide) 0xee (by decide)) pre_rip
  have f2 : InstrSpec 0x125f80 [0xC1, 0xE5, 0x08] (fun s => s.RIP = 0x125f80) (shlR32Effect 0x125f80 3 5 8)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR32Effect_footprint 0x125f80 3 5 8).toInstrSpec (shl_r32_imm8_effect_step 0x125f80 0xe5 0x8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x125f83 [0x44, 0x09, 0xE5] (fun s => s.RIP = 0x125f83) (orR32R32Effect 0x125f83 3 5 12)
      [.gpr 5, .gpr 12] [] [.reg 5, .flags, .rip] :=
    (orR32R32Effect_footprint 0x125f83 3 5 12).toInstrSpec (or_r32_r32_rex_effect_step 0x125f83 0x44 0xe5 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x125f86 [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x125f86) (movzxR32R8Effect 0x125f86 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x125f86 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x125f86 0xd2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x125f89 [0x09, 0xEA] (fun s => s.RIP = 0x125f89) (orR32R32Effect 0x125f89 2 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (orR32R32Effect_footprint 0x125f89 2 2 5).toInstrSpec (or_r32_r32_effect_step 0x125f89 0xea (by decide)) pre_rip
  have f6 : InstrSpec 0x125f8b [0x45, 0x0F, 0xB7, 0xC0] (fun s => s.RIP = 0x125f8b) (movzxR32R16Effect 0x125f8b 4 8 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (movzxR32R16Effect_footprint 0x125f8b 4 8 8).toInstrSpec (movzx_r32_r16_rex_effect_step 0x125f8b 0x45 (by decide) 0xc0 (by decide)) pre_rip
  have f7 : InstrSpec 0x125f8f [0x49, 0xC1, 0xE0, 0x30] (fun s => s.RIP = 0x125f8f) (shlR64Effect 0x125f8f 4 8 48)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x125f8f 4 8 48).toInstrSpec (shl_r64_imm8_effect_step 0x125f8f 0x49 0xe0 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x125f93 [0x45, 0x0F, 0xB6, 0xDB] (fun s => s.RIP = 0x125f93) (movzxR32R8Effect 0x125f93 4 11 11)
      [.gpr 11] [] [.reg 11, .rip] :=
    (movzxR32R8Effect_footprint 0x125f93 4 11 11).toInstrSpec (movzx_r32_r8_rex_effect_step 0x125f93 0x45 (by decide) 0xdb (by decide)) pre_rip
  have f9 : InstrSpec 0x125f97 [0x49, 0xC1, 0xE3, 0x28] (fun s => s.RIP = 0x125f97) (shlR64Effect 0x125f97 4 11 40)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR64Effect_footprint 0x125f97 4 11 40).toInstrSpec (shl_r64_imm8_effect_step 0x125f97 0x49 0xe3 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x125f9b [0x4D, 0x09, 0xC3] (fun s => s.RIP = 0x125f9b) (orR64R64Effect 0x125f9b 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x125f9b 11 8).toInstrSpec (or_r64_r64_effect_step 0x125f9b 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x125f9e [0x45, 0x0F, 0xB6, 0xC2] (fun s => s.RIP = 0x125f9e) (movzxR32R8Effect 0x125f9e 4 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movzxR32R8Effect_footprint 0x125f9e 4 8 10).toInstrSpec (movzx_r32_r8_rex_effect_step 0x125f9e 0x45 (by decide) 0xc2 (by decide)) pre_rip
  have f12 : InstrSpec 0x125fa2 [0x49, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x125fa2) (shlR64Effect 0x125fa2 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x125fa2 4 8 32).toInstrSpec (shl_r64_imm8_effect_step 0x125fa2 0x49 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x125fa6 [0x4D, 0x09, 0xD8] (fun s => s.RIP = 0x125fa6) (orR64R64Effect 0x125fa6 8 11)
      [.gpr 8, .gpr 11] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x125fa6 8 11).toInstrSpec (or_r64_r64_effect_step 0x125fa6 0x4d 0xd8 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x125fa9 [0x45, 0x89, 0xFA] (fun s => s.RIP = 0x125fa9) (movR32R32Effect 0x125fa9 3 10 15)
      [.gpr 15] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x125fa9 3 10 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x125fa9 0x45 0xfa (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x125fac [0x4D, 0x09, 0xC2] (fun s => s.RIP = 0x125fac) (orR64R64Effect 0x125fac 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x125fac 10 8).toInstrSpec (or_r64_r64_effect_step 0x125fac 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x125faf [0x45, 0x89, 0xC8] (fun s => s.RIP = 0x125faf) (movR32R32Effect 0x125faf 3 8 9)
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x125faf 3 8 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x125faf 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x125fb2 [0x4D, 0x09, 0xE8] (fun s => s.RIP = 0x125fb2) (orR64R64Effect 0x125fb2 8 13)
      [.gpr 8, .gpr 13] [] [.reg 8, .flags, .rip] :=
    (orR64R64Effect_footprint 0x125fb2 8 13).toInstrSpec (or_r64_r64_effect_step 0x125fb2 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x125fb5 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x42] (LoadPre 0x125fb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x125fb5 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125fb5 6 9 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x125fb5 6 9 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125fb5 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x125fbb [0x44, 0x88, 0x4B, 0x27] (StorePre 0x125fbb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x27)) s (0x125fbb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125fbb 4 9 (.base 3 (.d8 0x27)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x125fbb 4 9 (.base 3 (.d8 0x27))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125fbb 0x44 (by decide) 1 (.base 3 (.d8 0x27)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f7c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f80) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f83) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f86) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f89) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f8b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 65), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f8f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f93) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 69), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f97) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 71), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f9b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 67), (9, 9), (10, 10), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125f9e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 75), (9, 9), (10, 10), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fa2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 77), (9, 9), (10, 10), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fa6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 79), (9, 9), (10, 10), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fa9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 79), (9, 9), (10, 81), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fac) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 79), (9, 9), (10, 83), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125faf) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 85), (9, 9), (10, 83), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fb2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 9), (10, 83), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fb5) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 89), (10, 83), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fbb) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 87), (9, 89), (10, 83), (11, 73), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fbf) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l125f78_1 code

theorem block_l125f78 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125f78 :=
  Rest.liftedBlock (rest_l125f78 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125f78 x hx)

theorem rest_l125ff4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125ff4 bytes_l125ff4) (entryMap (live .l125ff4))
      9 0x125ff4 bytes_l125ff4 b_l125ff4 := by
  have f0 : InstrSpec 0x125ff4 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x125ff4) (movR64R64Effect 0x125ff4 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x125ff4 0 3).toInstrSpec (mov_r64_r64_effect_step 0x125ff4 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125ff7 [0x48, 0x81, 0xC4, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125ff7) (addR64Imm32Effect 0x125ff7 4 0xd8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x125ff7 4 0xd8).toInstrSpec (add_r64_imm32_effect_step 0x125ff7 0x48 0xc4 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x125ffe [0x5B] (PopPre 0x125ffe) (popR64Effect 0x125ffe 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x125ffe 1 3).toInstrSpec (pop_r64_effect_step 0x125ffe 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x125fff [0x41, 0x5C] (PopPre 0x125fff) (popR64Effect 0x125fff 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x125fff 2 12).toInstrSpec (pop_r64_rex_effect_step 0x125fff 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x126001 [0x41, 0x5D] (PopPre 0x126001) (popR64Effect 0x126001 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126001 2 13).toInstrSpec (pop_r64_rex_effect_step 0x126001 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x126003 [0x41, 0x5E] (PopPre 0x126003) (popR64Effect 0x126003 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126003 2 14).toInstrSpec (pop_r64_rex_effect_step 0x126003 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x126005 [0x41, 0x5F] (PopPre 0x126005) (popR64Effect 0x126005 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126005 2 15).toInstrSpec (pop_r64_rex_effect_step 0x126005 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x126007 [0x5D] (PopPre 0x126007) (popR64Effect 0x126007 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126007 1 5).toInstrSpec (pop_r64_effect_step 0x126007 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x126008 [0xC3] (RetPre 0x126008) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x126008).toInstrSpec (ret_effect_step 0x126008) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ff7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ffe) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125fff) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126001) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126003) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126005) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126007) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126008) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l125ff4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125ff4 :=
  Rest.liftedBlock (rest_l125ff4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125ff4 x hx)

theorem rest_l126009 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126009 bytes_l126009) (entryMap (live .l126009))
      12 0x126009 bytes_l126009 b_l126009 := by
  have f0 : InstrSpec 0x126009 [0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x126009 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126009 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126009 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126009 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x126009 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12600d [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x12600d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12600d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12600d 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12600d 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12600d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126012 [0x48, 0x8B, 0x6C, 0x24, 0x18] (LoadPre 0x126012 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126012 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126012 5 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x126012 5 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x126012 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126017 [0x4C, 0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x126017 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126017 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126017 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x126017 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x126017 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12601c [0x8B, 0x74, 0x24, 0x28] (LoadPre 0x12601c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12601c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12601c 6 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x12601c 6 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x12601c 6 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126020 [0x0F, 0xB6, 0x7C, 0x24, 0x2C] (LoadPre 0x126020 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x126020 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x126020 5 7 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x126020 5 7 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (movzx_r32_m8_effect_step 0x126020 7 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x126025 [0x4C, 0x8B, 0x44, 0x24, 0x2D] (LoadPre 0x126025 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x126025 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126025 8 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126025 8 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (mov_r64_m64_effect_step 0x126025 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x12602a [0x4C, 0x89, 0x44, 0x24, 0x58] (StorePre 0x12602a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12602a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12602a 8 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12602a 8 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x12602a 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12602f [0x4C, 0x8B, 0x44, 0x24, 0x35] (LoadPre 0x12602f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x12602f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12602f 8 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x12602f 8 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (mov_r64_m64_effect_step 0x12602f 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126034 [0x4C, 0x89, 0x44, 0x24, 0x60] (StorePre 0x126034 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126034 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126034 8 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126034 8 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x126034 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x126039 [0x44, 0x8B, 0x44, 0x24, 0x3C] (LoadPre 0x126039 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x126039 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126039 8 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x126039 8 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_effect_step 0x126039 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x12603e [0x44, 0x89, 0x44, 0x24, 0x67] (StorePre 0x12603e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x12603e + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12603e 8 (.sib 4 none 0 (.d8 0x67)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x12603e 8 (.sib 4 none 0 (.d8 0x67))).toInstrSpec (mov_m32_r32_effect_step 0x12603e 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x67)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12600d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126012) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126017) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12601c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126020) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126025) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 65), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12602a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 65), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12602f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 68), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126034) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 68), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126039) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 71), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12603e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 71), (9, 59), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126043) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l126009 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126009 :=
  Rest.liftedBlock (rest_l126009 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126009 x hx)

theorem rest_l126043 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126043 bytes_l126043) (entryMap (live .l126043))
      3 0x126043 bytes_l126043 b_l126043 := by
  have f0 : InstrSpec 0x126043 [0x49, 0x89, 0xE8] (fun s => s.RIP = 0x126043) (movR64R64Effect 0x126043 8 5)
      [.gpr 5] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x126043 8 5).toInstrSpec (mov_r64_r64_effect_step 0x126043 0x49 0xe8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126046 [0x4D, 0x21, 0xE8] (fun s => s.RIP = 0x126046) (andR64R64Effect 0x126046 8 13)
      [.gpr 8, .gpr 13] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x126046 8 13).toInstrSpec (and_r64_r64_effect_step 0x126046 0x4d 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126046) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126049) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x126049 0x2b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126043 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126043 :=
  Rest.liftedBlock (rest_l126043 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126043 x hx)

theorem rest_l12604b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12604b bytes_l12604b) (entryMap (live .l12604b))
      5 0x12604b bytes_l12604b b_l12604b := by
  have f0 : InstrSpec 0x12604b [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x12604b) (incR64Effect 0x12604b 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x12604b 0).toInstrSpec (inc_r64_effect_step 0x12604b 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12604e [0x49, 0x89, 0x46, 0x10] (StorePre 0x12604e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x12604e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12604e 0 (.base 14 (.d8 0x10)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x12604e 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12604e 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x126052 [0x45, 0x8B, 0x66, 0x18] (LoadPre 0x126052 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126052 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126052 12 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x126052 12 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x126052 0x45 (by decide) 4 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126056 [0x44, 0x39, 0xE5] (fun s => s.RIP = 0x126056) (cmpR32R32Effect 0x126056 3 5 12)
      [.gpr 5, .gpr 12] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x126056 3 5 12).toInstrSpec (cmp_r32_r32_rex_effect_step 0x126056 0x44 0xe5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12604e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126052) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126056) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126059) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x126059 6 0x64) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12604b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12604b :=
  Rest.liftedBlock (rest_l12604b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12604b x hx)

theorem rest_l12605b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12605b bytes_l12605b) (entryMap (live .l12605b))
      3 0x12605b bytes_l12605b b_l12605b := by
  have f0 : InstrSpec 0x12605b [0x41, 0x8D, 0x4C, 0x24, 0x01] (fun s => s.RIP = 0x12605b) (leaR32Effect 0x12605b 5 1 (.sib 12 none 0 (.d8 0x1)))
      [.gpr 12] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x12605b 5 1 (.sib 12 none 0 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x12605b 0x41 (by decide) 1 (.sib 12 none 0 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126060 [0x48, 0xC1, 0xE1, 0x20] (fun s => s.RIP = 0x126060) (shlR64Effect 0x126060 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x126060 4 1 32).toInstrSpec (shl_r64_imm8_effect_step 0x126060 0x48 0xe1 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126064 [0x48, 0x83, 0xC9, 0x03] (fun s => s.RIP = 0x126064) (orR64Imm8Effect 0x126064 1 0x3)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x126064 1 0x3).toInstrSpec (or_r64_imm8_effect_step 0x126064 0x48 0xc9 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126060) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126064) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126068) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l12605b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12605b :=
  Rest.liftedBlock (rest_l12605b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12605b x hx)

theorem rest_l126068 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126068 bytes_l126068) (entryMap (live .l126068))
      4 0x126068 bytes_l126068 b_l126068 := by
  have f0 : InstrSpec 0x126068 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126068) (movR32Imm32Effect 0x126068 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x126068 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x126068 0xb8 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x12606d [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x12606d) (xorR32R32Effect 0x12606d 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12606d 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x12606d 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126070 [0x44, 0x89, 0xE2] (fun s => s.RIP = 0x126070) (movR32R32Effect 0x126070 3 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x126070 3 2 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x126070 0x44 0xe2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126073 [0x44, 0x89, 0xE5] (fun s => s.RIP = 0x126073) (movR32R32Effect 0x126073 3 5 12)
      [.gpr 12] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x126073 3 5 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x126073 0x44 0xe5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12606d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126070) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126073) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 59), (6, 6), (7, 7), (8, 55), (9, 9), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126076) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l126068 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126068 :=
  Rest.liftedBlock (rest_l126068 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126068 x hx)

theorem rest_l126076 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126076 bytes_l126076) (entryMap (live .l126076))
      18 0x126076 bytes_l126076 b_l126076 := by
  have f0 : InstrSpec 0x126076 [0x44, 0x8B, 0x54, 0x24, 0x67] (LoadPre 0x126076 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x126076 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126076 10 (.sib 4 none 0 (.d8 0x67)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x126076 10 (.sib 4 none 0 (.d8 0x67))).toInstrSpec (mov_r32_m32_effect_step 0x126076 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x67)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12607b [0x44, 0x89, 0x54, 0x24, 0x4F] (StorePre 0x12607b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x12607b + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x12607b 10 (.sib 4 none 0 (.d8 0x4f)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x12607b 10 (.sib 4 none 0 (.d8 0x4f))).toInstrSpec (mov_m32_r32_effect_step 0x12607b 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x126080 [0x4C, 0x8B, 0x54, 0x24, 0x58] (LoadPre 0x126080 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126080 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126080 10 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x126080 10 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x126080 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126085 [0x4C, 0x8B, 0x5C, 0x24, 0x60] (LoadPre 0x126085 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126085 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126085 11 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x126085 11 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x126085 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12608a [0x4C, 0x89, 0x5C, 0x24, 0x48] (StorePre 0x12608a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12608a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12608a 11 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12608a 11 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x12608a 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12608f [0x4C, 0x89, 0x54, 0x24, 0x40] (StorePre 0x12608f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12608f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12608f 10 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12608f 10 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x12608f 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126094 [0x41, 0x89, 0xD6] (fun s => s.RIP = 0x126094) (movR32R32Effect 0x126094 3 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x126094 3 14 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x126094 0x41 0xd6 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x126097 [0x41, 0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x126097) (shrR32Effect 0x126097 4 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR32Effect_footprint 0x126097 4 14 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x126097 0x41 0xee 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12609b [0x41, 0x89, 0xD4] (fun s => s.RIP = 0x12609b) (movR32R32Effect 0x12609b 3 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x12609b 3 12 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x12609b 0x41 0xd4 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12609e [0x41, 0xC1, 0xEC, 0x10] (fun s => s.RIP = 0x12609e) (shrR32Effect 0x12609e 4 12 16)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x12609e 4 12 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x12609e 0x41 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1260a2 [0x4D, 0x89, 0xC2] (fun s => s.RIP = 0x1260a2) (movR64R64Effect 0x1260a2 10 8)
      [.gpr 8] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1260a2 10 8).toInstrSpec (mov_r64_r64_effect_step 0x1260a2 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1260a5 [0x49, 0xC1, 0xEA, 0x20] (fun s => s.RIP = 0x1260a5) (shrR64Effect 0x1260a5 4 10 32)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR64Effect_footprint 0x1260a5 4 10 32).toInstrSpec (shr_r64_imm8_effect_step 0x1260a5 0x49 0xea 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1260a9 [0x4D, 0x89, 0xC3] (fun s => s.RIP = 0x1260a9) (movR64R64Effect 0x1260a9 11 8)
      [.gpr 8] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1260a9 11 8).toInstrSpec (mov_r64_r64_effect_step 0x1260a9 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1260ac [0x49, 0xC1, 0xEB, 0x28] (fun s => s.RIP = 0x1260ac) (shrR64Effect 0x1260ac 4 11 40)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64Effect_footprint 0x1260ac 4 11 40).toInstrSpec (shr_r64_imm8_effect_step 0x1260ac 0x49 0xeb 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1260b0 [0x49, 0xC1, 0xE8, 0x30] (fun s => s.RIP = 0x1260b0) (shrR64Effect 0x1260b0 4 8 48)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x1260b0 4 8 48).toInstrSpec (shr_r64_imm8_effect_step 0x1260b0 0x49 0xe8 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1260b4 [0x4D, 0x21, 0xCD] (fun s => s.RIP = 0x1260b4) (andR64R64Effect 0x1260b4 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1260b4 13 9).toInstrSpec (and_r64_r64_effect_step 0x1260b4 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1260b7 [0x41, 0x89, 0xEF] (fun s => s.RIP = 0x1260b7) (movR32R32Effect 0x1260b7 3 15 5)
      [.gpr 5] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x1260b7 3 15 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x1260b7 0x41 0xef (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12607b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126080) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 56), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126085) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 56), (11, 58), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12608a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 56), (11, 58), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12608f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 56), (11, 58), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126094) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 56), (11, 58), (13, 13), (14, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126097) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 56), (11, 58), (13, 13), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12609b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 56), (11, 58), (12, 66), (13, 13), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12609e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 56), (11, 58), (12, 68), (13, 13), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260a2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 70), (11, 58), (12, 68), (13, 13), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260a5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 72), (11, 58), (12, 68), (13, 13), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260a9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 72), (11, 74), (12, 68), (13, 13), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260ac) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 72), (11, 76), (12, 68), (13, 13), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260b0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 78), (9, 9), (10, 72), (11, 76), (12, 68), (13, 13), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260b4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 78), (9, 9), (10, 72), (11, 76), (12, 68), (13, 80), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260b7) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 78), (9, 9), (10, 72), (11, 76), (12, 68), (13, 80), (14, 64), (15, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260ba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 84) (jmp_rel32_effect_step 0x1260ba 0xfffffeb9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126076 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126076 :=
  Rest.liftedBlock (rest_l126076 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126076 x hx)

theorem rest_l1260bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1260bf bytes_l1260bf) (entryMap (live .l1260bf))
      4 0x1260bf bytes_l1260bf b_l1260bf := by
  have f0 : InstrSpec 0x1260bf [0x41, 0x89, 0x6E, 0x18] (StorePre 0x1260bf 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1260bf + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1260bf 5 (.base 14 (.d8 0x18)))
      [.gpr 5, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x1260bf 5 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x1260bf 0x41 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1260c3 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x1260c3) (leaR64Effect 0x1260c3 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1260c3 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1260c3 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1260c8 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1260c8) (movR64R64Effect 0x1260c8 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1260c8 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1260c8 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1260cb [0xE8, 0x80, 0xF3, 0xFF, 0xFF] (PushPre 0x1260cb 5) (callEffect (fun _ => 0x125450) 0x1260d0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1260cb 0x125450 0x1260d0).toInstrSpec (call_rel32_effect_step 0x1260cb 0xfffff380 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260c8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260cb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125450) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 60) (by decide) (by decide) rfl rfl

theorem block_l1260bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1260bf :=
  Rest.liftedBlock (rest_l1260bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1260bf x hx)

theorem rest_l1260d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1260d0 bytes_l1260d0) (entryMap (live .l1260d0))
      7 0x1260d0 bytes_l1260d0 b_l1260d0 := by
  have f0 : InstrSpec 0x1260d0 [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1260d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1260d0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1260d0 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1260d0 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1260d0 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1260d4 [0x48, 0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x1260d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1260d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1260d4 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1260d4 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x1260d4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1260d9 [0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x1260d9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1260d9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1260d9 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1260d9 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x1260d9 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1260e1 [0x48, 0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x1260e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1260e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1260e1 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1260e1 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x1260e1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1260e6 [0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x1260e6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1260e6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1260e6 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1260e6 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x1260e6 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1260ee [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1260ee) (cmpR32Imm8Effect 0x1260ee 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1260ee 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1260ee 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260d9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260e1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260e6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260ee) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260f1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x1260f1 5 0x5c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1260d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1260d0 :=
  Rest.liftedBlock (rest_l1260d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1260d0 x hx)

theorem rest_l1260f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1260f3 bytes_l1260f3) (entryMap (live .l1260f3))
      7 0x1260f3 bytes_l1260f3 b_l1260f3 := by
  have f0 : InstrSpec 0x1260f3 [0x48, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x1260f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1260f3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1260f3 6 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1260f3 6 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x1260f3 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1260fb [0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x1260fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1260fb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1260fb 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1260fb 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x1260fb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126103 [0x48, 0x89, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x126103 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x126103 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126103 6 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126103 6 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x126103 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x12610b [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x12610b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x12610b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12610b 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12610b 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x12610b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x126113 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x126113) (leaR64Effect 0x126113 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x126113 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x126113 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x126118 [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126118) (movR32Imm32Effect 0x126118 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x126118 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x126118 0xba (by decide) 0x2) pre_rip
  have f6 : InstrSpec 0x12611d [0xE8, 0xAE, 0x15, 0x00, 0x00] (PushPre 0x12611d 5) (callEffect (fun _ => 0x1276d0) 0x126122)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12611d 0x1276d0 0x126122).toInstrSpec (call_rel32_effect_step 0x12611d 0x15ae (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1260fb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126103) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12610b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126113) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126118) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12611d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l1260f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1260f3 :=
  Rest.liftedBlock (rest_l1260f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1260f3 x hx)

theorem rest_l126122 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126122 bytes_l126122) (entryMap (live .l126122))
      3 0x126122 bytes_l126122 b_l126122 := by
  have f0 : InstrSpec 0x126122 [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x126122 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126122 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126122 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x126122 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x126122 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126126 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x126126) (cmpR32Imm8Effect 0x126126 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126126 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126126 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126126) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126129) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x126129 5 0x7f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126122 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126122 :=
  Rest.liftedBlock (rest_l126122 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126122 x hx)

theorem rest_l12612b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12612b bytes_l12612b) (entryMap (live .l12612b))
      4 0x12612b bytes_l12612b b_l12612b := by
  have f0 : InstrSpec 0x12612b [0x48, 0x8D, 0x7C, 0x24, 0x70] (fun s => s.RIP = 0x12612b) (leaR64Effect 0x12612b 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12612b 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (lea_r64_effect_step 0x12612b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126130 [0x48, 0x8D, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126130) (leaR64Effect 0x126130 2 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x126130 2 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (lea_r64_effect_step 0x126130 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126138 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x126138) (movR64R64Effect 0x126138 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x126138 6 14).toInstrSpec (mov_r64_r64_effect_step 0x126138 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12613b [0xE8, 0xE0, 0x0B, 0x00, 0x00] (PushPre 0x12613b 5) (callEffect (fun _ => 0x126d20) 0x126140)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12613b 0x126d20 0x126140).toInstrSpec (call_rel32_effect_step 0x12613b 0xbe0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126130) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126138) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12613b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126d20) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l12612b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12612b :=
  Rest.liftedBlock (rest_l12612b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12612b x hx)

theorem rest_l126140 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126140 bytes_l126140) (entryMap (live .l126140))
      4 0x126140 bytes_l126140 b_l126140 := by
  have f0 : InstrSpec 0x126140 [0x8B, 0x44, 0x24, 0x70] (LoadPre 0x126140 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126140 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126140 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x126140 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r32_m32_low_effect_step 0x126140 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126144 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x126144) (cmpR32Imm8Effect 0x126144 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126144 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126144 0xf8 0x2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126147 [0x0F, 0x95, 0xC1] (fun s => s.RIP = 0x126147) (atFlags (condHolds 5) (setccR8Effect 0x126147 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x126147 3 1 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x126147 5 0xc1 (by decide) (by decide) c)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126144) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126147) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12614a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x12614a 0xb0 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126140 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126140 :=
  Rest.liftedBlock (rest_l126140 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126140 x hx)

theorem rest_l12614f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12614f bytes_l12614f) (entryMap (live .l12614f))
      15 0x12614f bytes_l12614f b_l12614f := by
  have f0 : InstrSpec 0x12614f [0x8B, 0x4C, 0x24, 0x3C] (LoadPre 0x12614f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x12614f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12614f 1 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12614f 1 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x12614f 1 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126153 [0x89, 0x8C, 0x24, 0xA4, 0x00, 0x00, 0x00] (StorePre 0x126153 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x126153 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x126153 1 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126153 1 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (mov_m32_r32_low_effect_step 0x126153 1 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12615a [0x48, 0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x12615a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12615a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12615a 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12615a 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x12615a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12615f [0x48, 0x89, 0x8C, 0x24, 0x9C, 0x00, 0x00, 0x00] (StorePre 0x12615f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x12615f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12615f 1 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12615f 1 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (mov_m64_r64_effect_step 0x12615f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x126167 [0x48, 0x8B, 0x4C, 0x24, 0x2C] (LoadPre 0x126167 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x126167 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126167 1 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126167 1 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x126167 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12616c [0x48, 0x89, 0x8C, 0x24, 0x94, 0x00, 0x00, 0x00] (StorePre 0x12616c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x12616c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12616c 1 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12616c 1 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (mov_m64_r64_effect_step 0x12616c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126174 [0x48, 0x8B, 0x4C, 0x24, 0x1C] (LoadPre 0x126174 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x126174 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126174 1 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126174 1 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x126174 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x126179 [0x48, 0x8B, 0x54, 0x24, 0x24] (LoadPre 0x126179 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x126179 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126179 2 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126179 2 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x126179 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x12617e [0x48, 0x89, 0x94, 0x24, 0x8C, 0x00, 0x00, 0x00] (StorePre 0x12617e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x12617e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12617e 2 (.sib 4 none 0 (.d32 0x8c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12617e 2 (.sib 4 none 0 (.d32 0x8c))).toInstrSpec (mov_m64_r64_effect_step 0x12617e 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x8c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x126186 [0x48, 0x89, 0x8C, 0x24, 0x84, 0x00, 0x00, 0x00] (StorePre 0x126186 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x126186 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126186 1 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126186 1 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_m64_r64_effect_step 0x126186 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x12618e [0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x12618e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x12618e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12618e 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12618e 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x12618e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x126196 [0x48, 0x8B, 0x94, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x126196 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x126196 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126196 2 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126196 2 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x126196 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12619e [0x48, 0x89, 0x4C, 0x24, 0x74] (StorePre 0x12619e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x12619e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12619e 1 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12619e 1 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m64_r64_effect_step 0x12619e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1261a3 [0x48, 0x89, 0x54, 0x24, 0x7C] (StorePre 0x1261a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1261a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1261a3 2 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1261a3 2 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m64_r64_effect_step 0x1261a3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126153) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12615a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12615f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126167) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12616c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126174) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126179) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12617e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126186) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12618e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 64), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126196) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12619e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261a3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261a8) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 74) (jmp_rel8_effect_step 0x1261a8 0x53 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12614f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12614f :=
  Rest.liftedBlock (rest_l12614f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12614f x hx)

theorem rest_l1261aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1261aa bytes_l1261aa) (entryMap (live .l1261aa))
      14 0x1261aa bytes_l1261aa b_l1261aa := by
  have f0 : InstrSpec 0x1261aa [0x48, 0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x1261aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1261aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261aa 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1261aa 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x1261aa 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1261af [0x48, 0x8B, 0x54, 0x24, 0x14] (LoadPre 0x1261af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1261af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261af 2 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1261af 2 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x1261af 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1261b4 [0x48, 0x89, 0x54, 0x24, 0x7C] (StorePre 0x1261b4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1261b4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1261b4 2 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1261b4 2 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m64_r64_effect_step 0x1261b4 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1261b9 [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x1261b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1261b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261b9 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1261b9 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x1261b9 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1261be [0x48, 0x89, 0x94, 0x24, 0x84, 0x00, 0x00, 0x00] (StorePre 0x1261be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x1261be + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1261be 2 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1261be 2 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_m64_r64_effect_step 0x1261be 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1261c6 [0x48, 0x8B, 0x54, 0x24, 0x24] (LoadPre 0x1261c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1261c6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261c6 2 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1261c6 2 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x1261c6 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1261cb [0x48, 0x89, 0x94, 0x24, 0x8C, 0x00, 0x00, 0x00] (StorePre 0x1261cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x1261cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1261cb 2 (.sib 4 none 0 (.d32 0x8c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1261cb 2 (.sib 4 none 0 (.d32 0x8c))).toInstrSpec (mov_m64_r64_effect_step 0x1261cb 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x8c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1261d3 [0x48, 0x8B, 0x54, 0x24, 0x2C] (LoadPre 0x1261d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1261d3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261d3 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1261d3 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x1261d3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1261d8 [0x48, 0x89, 0x94, 0x24, 0x94, 0x00, 0x00, 0x00] (StorePre 0x1261d8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x1261d8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1261d8 2 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1261d8 2 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (mov_m64_r64_effect_step 0x1261d8 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1261e0 [0x48, 0x8B, 0x54, 0x24, 0x34] (LoadPre 0x1261e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1261e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1261e0 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1261e0 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x1261e0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1261e5 [0x48, 0x89, 0x94, 0x24, 0x9C, 0x00, 0x00, 0x00] (StorePre 0x1261e5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x1261e5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1261e5 2 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1261e5 2 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (mov_m64_r64_effect_step 0x1261e5 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1261ed [0x8B, 0x54, 0x24, 0x3C] (LoadPre 0x1261ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1261ed + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1261ed 2 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1261ed 2 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x1261ed 2 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1261f1 [0x89, 0x94, 0x24, 0xA4, 0x00, 0x00, 0x00] (StorePre 0x1261f1 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x1261f1 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1261f1 2 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1261f1 2 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1261f1 2 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1261f8 [0x48, 0x89, 0x4C, 0x24, 0x74] (StorePre 0x1261f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x1261f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1261f8 1 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1261f8 1 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m64_r64_effect_step 0x1261f8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261af) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261b4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261b9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261be) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261c6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261cb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261d3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261d8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261e0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261e5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261ed) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261f1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261f8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261fd) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l1261aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1261aa :=
  Rest.liftedBlock (rest_l1261aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1261aa x hx)

theorem rest_l1261fd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1261fd bytes_l1261fd) (entryMap (live .l1261fd))
      1 0x1261fd bytes_l1261fd b_l1261fd := by
  have f0 : InstrSpec 0x1261fd [0xB1, 0x01] (fun s => s.RIP = 0x1261fd) (movR8Imm8Effect 0x1261fd 2 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x1261fd 2 1 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x1261fd 0xb1 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1261ff) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1261fd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1261fd :=
  Rest.liftedBlock (rest_l1261fd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1261fd x hx)

theorem rest_l1261ff [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1261ff bytes_l1261ff) (entryMap (live .l1261ff))
      15 0x1261ff bytes_l1261ff b_l1261ff := by
  have f0 : InstrSpec 0x1261ff [0x41, 0x8B, 0x6E, 0x18] (LoadPre 0x1261ff (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1261ff + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1261ff 5 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 5, .rip] :=
    (movR32M32Effect_footprint 0x1261ff 5 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x1261ff 0x41 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126203 [0x41, 0x8B, 0x56, 0x1C] (LoadPre 0x126203 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126203 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126203 2 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR32M32Effect_footprint 0x126203 2 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x126203 0x41 (by decide) 2 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126207 [0x29, 0xD5] (fun s => s.RIP = 0x126207) (subR32R32Effect 0x126207 2 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (subR32R32Effect_footprint 0x126207 2 5 2).toInstrSpec (sub_r32_r32_effect_step 0x126207 0xd5 (by decide)) pre_rip
  have f3 : InstrSpec 0x126209 [0x40, 0x0F, 0x96, 0xC6] (fun s => s.RIP = 0x126209) (atFlags (condHolds 6) (setccR8Effect 0x126209 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x126209 4 6 6).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x126209 6 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f4 : InstrSpec 0x12620d [0x48, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x12620d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x12620d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12620d 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12620d 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x12620d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126215 [0x49, 0x89, 0x3E] (StorePre 0x126215 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126215 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126215 7 (.base 14 .none))
      [.gpr 7, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126215 7 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x126215 0x49 (by decide) 7 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126218 [0x48, 0x8B, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x126218 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x126218 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126218 7 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126218 7 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x126218 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x126220 [0x49, 0x89, 0x7E, 0x08] (StorePre 0x126220 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126220 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126220 7 (.base 14 (.d8 0x8)))
      [.gpr 7, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126220 7 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126220 0x49 (by decide) 7 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126224 [0x45, 0x89, 0x66, 0x18] (StorePre 0x126224 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126224 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126224 12 (.base 14 (.d8 0x18)))
      [.gpr 12, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x126224 12 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x126224 0x45 (by decide) 4 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x126228 [0x49, 0x8B, 0x7E, 0x10] (LoadPre 0x126228 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126228 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126228 7 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x126228 7 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x126228 0x49 (by decide) 7 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x12622c [0x48, 0x83, 0xFF, 0x01] (fun s => s.RIP = 0x12622c) (cmpR64Imm8Effect 0x12622c 7 0x1)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12622c 7 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x12622c 0x48 0xff 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x126230 [0x48, 0x83, 0xD7, 0xFF] (fun s => s.RIP = 0x126230) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126230 7 0xff))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 7, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x126230 7 0xff).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x126230 0x48 0xd7 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f12 : InstrSpec 0x126234 [0x49, 0x89, 0x7E, 0x10] (StorePre 0x126234 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126234 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126234 7 (.base 14 (.d8 0x10)))
      [.gpr 7, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x126234 7 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126234 0x49 (by decide) 7 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x126238 [0x40, 0x08, 0xCE] (fun s => s.RIP = 0x126238) (orR8R8Effect 0x126238 3 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (orR8R8Effect_footprint 0x126238 3 6 1).toInstrSpec (or_r8_r8_rex_effect_step 0x126238 0x40 0xce (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126203) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126207) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 59) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126209) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12620d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126215) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126218) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126220) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126224) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126228) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12622c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126230) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126234) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 61), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126238) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 57), (6, 77), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12623b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 80) (jcc_rel8_effect_step 0x12623b 4 0x77) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1261ff [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1261ff :=
  Rest.liftedBlock (rest_l1261ff code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1261ff x hx)

theorem rest_l12623d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12623d bytes_l12623d) (entryMap (live .l12623d))
      14 0x12623d bytes_l12623d b_l12623d := by
  have f0 : InstrSpec 0x12623d [0x8B, 0x54, 0x24, 0x74] (LoadPre 0x12623d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x12623d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12623d 2 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x12623d 2 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_r32_m32_low_effect_step 0x12623d 2 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126241 [0x48, 0x8B, 0x4C, 0x24, 0x78] (LoadPre 0x126241 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126241 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126241 1 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126241 1 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x126241 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126246 [0x48, 0x8B, 0xAC, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x126246 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126246 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126246 5 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x126246 5 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x126246 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12624e [0x4C, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x12624e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x12624e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12624e 9 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x12624e 9 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x12624e 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126256 [0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x126256 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126256 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x126256 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x126256 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r32_m32_low_effect_step 0x126256 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12625d [0x0F, 0xB6, 0xBC, 0x24, 0x94, 0x00, 0x00, 0x00] (LoadPre 0x12625d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x12625d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x12625d 8 7 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x12625d 8 7 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (movzx_r32_m8_effect_step 0x12625d 7 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x126265 [0x4C, 0x8B, 0x84, 0x24, 0x95, 0x00, 0x00, 0x00] (LoadPre 0x126265 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x95)) s (0x126265 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126265 8 (.sib 4 none 0 (.d32 0x95)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126265 8 (.sib 4 none 0 (.d32 0x95))).toInstrSpec (mov_r64_m64_effect_step 0x126265 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x95)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x12626d [0x4C, 0x89, 0x44, 0x24, 0x58] (StorePre 0x12626d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12626d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12626d 8 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12626d 8 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x12626d 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126272 [0x4C, 0x8B, 0x84, 0x24, 0x9D, 0x00, 0x00, 0x00] (LoadPre 0x126272 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9d)) s (0x126272 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126272 8 (.sib 4 none 0 (.d32 0x9d)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x126272 8 (.sib 4 none 0 (.d32 0x9d))).toInstrSpec (mov_r64_m64_effect_step 0x126272 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x9d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x12627a [0x4C, 0x89, 0x44, 0x24, 0x60] (StorePre 0x12627a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12627a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12627a 8 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12627a 8 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x12627a 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x12627f [0x44, 0x8B, 0x84, 0x24, 0xA4, 0x00, 0x00, 0x00] (LoadPre 0x12627f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x12627f + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x12627f 8 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x12627f 8 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (mov_r32_m32_effect_step 0x12627f 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x126287 [0x44, 0x89, 0x44, 0x24, 0x67] (StorePre 0x126287 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x67)) s (0x126287 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126287 8 (.sib 4 none 0 (.d8 0x67)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x126287 8 (.sib 4 none 0 (.d8 0x67))).toInstrSpec (mov_m32_r32_effect_step 0x126287 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x67)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12628c [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x12628c) (cmpR32Imm8Effect 0x12628c 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12628c 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x12628c 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126241) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126246) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12624e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126256) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12625d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126265) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 65), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12626d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 65), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126272) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 68), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12627a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 68), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12627f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 71), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126287) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 71), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12628c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 57), (6, 61), (7, 63), (8, 71), (9, 59), (10, 10), (11, 11), (13, 13), (15, 15), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12628f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 76) (jcc_rel32_effect_step 0x12628f 5 0xfffffdae) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12623d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12623d :=
  Rest.liftedBlock (rest_l12623d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12623d x hx)

theorem rest_l126295 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126295 bytes_l126295) (entryMap (live .l126295))
      7 0x126295 bytes_l126295 b_l126295 := by
  have f0 : InstrSpec 0x126295 [0x48, 0x89, 0x4B, 0x08] (StorePre 0x126295 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126295 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126295 1 (.base 3 (.d8 0x8)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126295 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126295 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126299 [0x48, 0x89, 0x6B, 0x10] (StorePre 0x126299 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126299 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126299 5 (.base 3 (.d8 0x10)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126299 5 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126299 0x48 (by decide) 5 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12629d [0x4C, 0x89, 0x4B, 0x18] (StorePre 0x12629d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x12629d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12629d 9 (.base 3 (.d8 0x18)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12629d 9 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12629d 0x4c (by decide) 1 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1262a1 [0x44, 0x89, 0x7B, 0x20] (StorePre 0x1262a1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1262a1 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1262a1 15 (.base 3 (.d8 0x20)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x1262a1 15 (.base 3 (.d8 0x20))).toInstrSpec (mov_m32_r32_effect_step 0x1262a1 0x44 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1262a5 [0xC6, 0x43, 0x24, 0x00] (StorePre 0x1262a5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x1262a5 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1262a5 (.base 3 (.d8 0x24)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1262a5 (.base 3 (.d8 0x24)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1262a5 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1262a9 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x1262a9 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1262a9 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1262a9 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1262a9 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x1262a9 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126299) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12629d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262a5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262a9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262af) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x1262af 0xfffffd40 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126295 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126295 :=
  Rest.liftedBlock (rest_l126295 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126295 x hx)

theorem rest_l1262b4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1262b4 bytes_l1262b4) (entryMap (live .l1262b4))
      7 0x1262b4 bytes_l1262b4 b_l1262b4 := by
  have f0 : InstrSpec 0x1262b4 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1262b4 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1262b4 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1262b4 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1262b4 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1262b4 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1262b9 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x1262b9) (movR64R64Effect 0x1262b9 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1262b9 1 2).toInstrSpec (mov_r64_r64_effect_step 0x1262b9 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1262bc [0x48, 0xC1, 0xE1, 0x20] (fun s => s.RIP = 0x1262bc) (shlR64Effect 0x1262bc 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x1262bc 4 1 32).toInstrSpec (shl_r64_imm8_effect_step 0x1262bc 0x48 0xe1 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1262c0 [0x48, 0x83, 0xC9, 0x13] (fun s => s.RIP = 0x1262c0) (orR64Imm8Effect 0x1262c0 1 0x13)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x1262c0 1 0x13).toInstrSpec (or_r64_imm8_effect_step 0x1262c0 0x48 0xc9 0x13 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1262c4 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1262c4) (movR32Imm32Effect 0x1262c4 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1262c4 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1262c4 0xb8 (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x1262c9 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1262c9) (xorR32R32Effect 0x1262c9 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1262c9 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1262c9 0x45 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262bc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 56), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262c0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262c4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262c9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 9), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262cc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 64) (jmp_rel32_effect_step 0x1262cc 0xfffffda5 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1262b4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1262b4 :=
  Rest.liftedBlock (rest_l1262b4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1262b4 x hx)

theorem rest_l1262d1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1262d1 bytes_l1262d1) (entryMap (live .l1262d1))
      4 0x1262d1 bytes_l1262d1 b_l1262d1 := by
  have f0 : InstrSpec 0x1262d1 [0x31, 0xC0] (fun s => s.RIP = 0x1262d1) (xorR32R32Effect 0x1262d1 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1262d1 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1262d1 0xc0 (by decide)) pre_rip
  have f1 : InstrSpec 0x1262d3 [0xB9, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1262d3) (movR32Imm32Effect 0x1262d3 5 1 0xc)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1262d3 5 1 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x1262d3 0xb9 (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x1262d8 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x1262d8) (xorR32R32Effect 0x1262d8 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1262d8 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1262d8 0x45 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262db) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x1262db 0xfffffd96 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1262d1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1262d1 :=
  Rest.liftedBlock (rest_l1262d1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1262d1 x hx)

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

theorem_by block_l125d50_eval :
    program.runBlock (dialect code) ⟨.l125d50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125d78_eval :
    program.runBlock (dialect code) ⟨.l125d78, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125d8a_eval :
    program.runBlock (dialect code) ⟨.l125d8a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125d92_eval :
    program.runBlock (dialect code) ⟨.l125d92, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125d9f_eval :
    program.runBlock (dialect code) ⟨.l125d9f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125dac_eval :
    program.runBlock (dialect code) ⟨.l125dac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125dcd_eval :
    program.runBlock (dialect code) ⟨.l125dcd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125dd7_eval :
    program.runBlock (dialect code) ⟨.l125dd7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125de1_eval :
    program.runBlock (dialect code) ⟨.l125de1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125dfc_eval :
    program.runBlock (dialect code) ⟨.l125dfc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125e1f_eval :
    program.runBlock (dialect code) ⟨.l125e1f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125e2c_eval :
    program.runBlock (dialect code) ⟨.l125e2c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125e4b_eval :
    program.runBlock (dialect code) ⟨.l125e4b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125e55_eval :
    program.runBlock (dialect code) ⟨.l125e55, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125e9c_eval :
    program.runBlock (dialect code) ⟨.l125e9c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125eab_eval :
    program.runBlock (dialect code) ⟨.l125eab, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125f11_eval :
    program.runBlock (dialect code) ⟨.l125f11, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125f19_eval :
    program.runBlock (dialect code) ⟨.l125f19, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125f4e_eval :
    program.runBlock (dialect code) ⟨.l125f4e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125f78_eval :
    program.runBlock (dialect code) ⟨.l125f78, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125ff4_eval :
    program.runBlock (dialect code) ⟨.l125ff4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126009_eval :
    program.runBlock (dialect code) ⟨.l126009, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126043_eval :
    program.runBlock (dialect code) ⟨.l126043, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12604b_eval :
    program.runBlock (dialect code) ⟨.l12604b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12605b_eval :
    program.runBlock (dialect code) ⟨.l12605b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126068_eval :
    program.runBlock (dialect code) ⟨.l126068, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126076_eval :
    program.runBlock (dialect code) ⟨.l126076, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1260bf_eval :
    program.runBlock (dialect code) ⟨.l1260bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1260d0_eval :
    program.runBlock (dialect code) ⟨.l1260d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1260f3_eval :
    program.runBlock (dialect code) ⟨.l1260f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126122_eval :
    program.runBlock (dialect code) ⟨.l126122, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12612b_eval :
    program.runBlock (dialect code) ⟨.l12612b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126140_eval :
    program.runBlock (dialect code) ⟨.l126140, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12614f_eval :
    program.runBlock (dialect code) ⟨.l12614f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1261aa_eval :
    program.runBlock (dialect code) ⟨.l1261aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1261fd_eval :
    program.runBlock (dialect code) ⟨.l1261fd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1261ff_eval :
    program.runBlock (dialect code) ⟨.l1261ff, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12623d_eval :
    program.runBlock (dialect code) ⟨.l12623d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126295_eval :
    program.runBlock (dialect code) ⟨.l126295, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1262b4_eval :
    program.runBlock (dialect code) ⟨.l1262b4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1262d1_eval :
    program.runBlock (dialect code) ⟨.l1262d1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
