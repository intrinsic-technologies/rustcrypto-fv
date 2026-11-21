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

theorem rest_l1262e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1262e0 bytes_l1262e0) (entryMap (live .l1262e0))
      13 0x1262e0 bytes_l1262e0 b_l1262e0 := by
  have f0 : InstrSpec 0x1262e0 [0x55] (PushPre 0x1262e0 1) (pushR64Effect 0x1262e0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1262e0 1 5).toInstrSpec (push_r64_effect_step 0x1262e0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1262e1 [0x41, 0x57] (PushPre 0x1262e1 2) (pushR64Effect 0x1262e1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1262e1 2 15).toInstrSpec (push_r64_rex_effect_step 0x1262e1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1262e3 [0x41, 0x56] (PushPre 0x1262e3 2) (pushR64Effect 0x1262e3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1262e3 2 14).toInstrSpec (push_r64_rex_effect_step 0x1262e3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1262e5 [0x41, 0x55] (PushPre 0x1262e5 2) (pushR64Effect 0x1262e5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1262e5 2 13).toInstrSpec (push_r64_rex_effect_step 0x1262e5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1262e7 [0x41, 0x54] (PushPre 0x1262e7 2) (pushR64Effect 0x1262e7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1262e7 2 12).toInstrSpec (push_r64_rex_effect_step 0x1262e7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1262e9 [0x53] (PushPre 0x1262e9 1) (pushR64Effect 0x1262e9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1262e9 1 3).toInstrSpec (push_r64_effect_step 0x1262e9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1262ea [0x48, 0x81, 0xEC, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1262ea) (subR64Imm32Effect 0x1262ea 4 0xb8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x1262ea 4 0xb8).toInstrSpec (sub_r64_imm32_effect_step 0x1262ea 0x48 0xec 0xb8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1262f1 [0x89, 0xD1] (fun s => s.RIP = 0x1262f1) (movR32R32Effect 0x1262f1 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1262f1 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x1262f1 0xd1 (by decide)) pre_rip
  have f8 : InstrSpec 0x1262f3 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x1262f3) (movR64R64Effect 0x1262f3 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1262f3 14 6).toInstrSpec (mov_r64_r64_effect_step 0x1262f3 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1262f6 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x1262f6) (movR64R64Effect 0x1262f6 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1262f6 3 7).toInstrSpec (mov_r64_r64_effect_step 0x1262f6 0x48 0xfb (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1262f9 [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x1262f9) (leaR64Effect 0x1262f9 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1262f9 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1262f9 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1262fe [0xBA, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1262fe) (movR32Imm32Effect 0x1262fe 5 2 0x80)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1262fe 5 2 0x80).toInstrSpec (mov_r32_imm32_effect_step 0x1262fe 0xba (by decide) 0x80) pre_rip
  have f12 : InstrSpec 0x126303 [0xE8, 0x88, 0xDF, 0xFF, 0xFF] (PushPre 0x126303 5) (callEffect (fun _ => 0x124290) 0x126308)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x126303 0x124290 0x126308).toInstrSpec (call_rel32_effect_step 0x126303 0xffffdf88 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262e1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262e5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262e7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262e9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262ea) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262f1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 67), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262f3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 67), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262f6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 67), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262f9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 67), (2, 2), (3, 71), (4, 65), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1262fe) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 67), (2, 75), (3, 71), (4, 65), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126303) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 67), (2, 75), (3, 71), (4, 77), (5, 5), (6, 6), (7, 73), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124290) f12 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l1262e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1262e0 :=
  Rest.liftedBlock (rest_l1262e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1262e0 x hx)

theorem rest_l126308 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126308 bytes_l126308) (entryMap (live .l126308))
      4 0x126308 bytes_l126308 b_l126308 := by
  have f0 : InstrSpec 0x126308 [0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x126308 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126308 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126308 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x126308 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x126308 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12630c [0x0F, 0xB6, 0x44, 0x24, 0x24] (LoadPre 0x12630c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12630c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12630c 5 0 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x12630c 5 0 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (movzx_r32_m8_effect_step 0x12630c 0 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126311 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x126311) (cmpR32Imm8Effect 0x126311 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126311 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126311 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12630c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126311) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126314) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x126314 5 0xbf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126308 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126308 :=
  Rest.liftedBlock (rest_l126308 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126308 x hx)

theorem rest_l12631a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12631a bytes_l12631a) (entryMap (live .l12631a))
      2 0x12631a bytes_l12631a b_l12631a := by
  have f0 : InstrSpec 0x12631a [0xA8, 0x01] (fun s => s.RIP = 0x12631a) (testAlImm8Effect 0x12631a 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x12631a 0x1).toInstrSpec (test_al_imm8_effect_step 0x12631a 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12631c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x12631c 4 0xfe) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12631a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12631a :=
  Rest.liftedBlock (rest_l12631a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12631a x hx)

theorem rest_l126322 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126322 bytes_l126322) (entryMap (live .l126322))
      3 0x126322 bytes_l126322 b_l126322 := by
  have f0 : InstrSpec 0x126322 [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x126322) (leaR64Effect 0x126322 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x126322 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x126322 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126327 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x126327) (movR64R64Effect 0x126327 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x126327 6 14).toInstrSpec (mov_r64_r64_effect_step 0x126327 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12632a [0xE8, 0x21, 0xF1, 0xFF, 0xFF] (PushPre 0x12632a 5) (callEffect (fun _ => 0x125450) 0x12632f)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12632a 0x125450 0x12632f).toInstrSpec (call_rel32_effect_step 0x12632a 0xfffff121 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126327) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12632a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125450) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l126322 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126322 :=
  Rest.liftedBlock (rest_l126322 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126322 x hx)

theorem rest_l12632f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12632f bytes_l12632f) (entryMap (live .l12632f))
      8 0x12632f bytes_l12632f b_l12632f := by
  have f0 : InstrSpec 0x12632f [0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x12632f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12632f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12632f 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12632f 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x12632f 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126333 [0x0F, 0xB6, 0x44, 0x24, 0x24] (LoadPre 0x126333 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x126333 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x126333 5 0 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x126333 5 0 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (movzx_r32_m8_effect_step 0x126333 0 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126338 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x25] (LoadPre 0x126338 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x126338 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126338 6 11 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x126338 6 11 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x126338 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12633e [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x26] (LoadPre 0x12633e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x12633e + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x12633e 6 10 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x12633e 6 10 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x12633e 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126344 [0x44, 0x8B, 0x6C, 0x24, 0x28] (LoadPre 0x126344 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126344 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126344 13 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x126344 13 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_effect_step 0x126344 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126349 [0x8B, 0x6C, 0x24, 0x2C] (LoadPre 0x126349 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x126349 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126349 5 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x126349 5 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r32_m32_low_effect_step 0x126349 5 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12634d [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x12634d) (cmpR32Imm8Effect 0x12634d 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12634d 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x12634d 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126333) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126338) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12633e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126344) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 57), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126349) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 57), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12634d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 57), (13, 61), (14, 14), (15, 15), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126350) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel32_effect_step 0x126350 5 0xd9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12632f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12632f :=
  Rest.liftedBlock (rest_l12632f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12632f x hx)

theorem rest_l126356 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126356 bytes_l126356) (entryMap (live .l126356))
      4 0x126356 bytes_l126356 b_l126356 := by
  have f0 : InstrSpec 0x126356 [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x126356) (movzxR32R8Effect 0x126356 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x126356 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x126356 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126359 [0x8D, 0x51, 0xEA] (fun s => s.RIP = 0x126359) (leaR32Effect 0x126359 3 2 (.base 1 (.d8 0xea)))
      [.gpr 1] [] [.reg 2, .rip] :=
    (leaR32Effect_footprint 0x126359 3 2 (.base 1 (.d8 0xea))).toInstrSpec (lea_r32_effect_step 0x126359 2 (.base 1 (.d8 0xea)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12635c [0x83, 0xFA, 0x03] (fun s => s.RIP = 0x12635c) (cmpR32Imm8Effect 0x12635c 3 2 0x3)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12635c 3 2 0x3).toInstrSpec (cmp_r32_imm8_effect_step 0x12635c 0xfa 0x3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126359) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12635c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12635f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x12635f 3 0x11b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126356 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126356 :=
  Rest.liftedBlock (rest_l126356 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126356 x hx)

theorem rest_l126365 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126365 bytes_l126365) (entryMap (live .l126365))
      2 0x126365 bytes_l126365 b_l126365 := by
  have f0 : InstrSpec 0x126365 [0x41, 0xF6, 0xC3, 0x01] (fun s => s.RIP = 0x126365) (testR8Imm8Effect 0x126365 11 0x1)
      [.gpr 11] [] [.flags, .rip] :=
    (testR8Imm8Effect_footprint 0x126365 11 0x1).toInstrSpec (test_r8_imm8_effect_step 0x126365 0x41 0xc3 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126369) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x126369 4 0x152) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126365 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126365 :=
  Rest.liftedBlock (rest_l126365 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126365 x hx)

theorem rest_l12636f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12636f bytes_l12636f) (entryMap (live .l12636f))
      2 0x12636f bytes_l12636f b_l12636f := by
  have f0 : InstrSpec 0x12636f [0x3C, 0x17] (fun s => s.RIP = 0x12636f) (cmpAlImm8Effect 0x12636f 0x17)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x12636f 0x17).toInstrSpec (cmp_al_imm8_effect_step 0x12636f 0x17) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126371) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x126371 5 0x111) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12636f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12636f :=
  Rest.liftedBlock (rest_l12636f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12636f x hx)

theorem rest_l126377 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126377 bytes_l126377) (entryMap (live .l126377))
      3 0x126377 bytes_l126377 b_l126377 := by
  have f0 : InstrSpec 0x126377 [0x45, 0x8B, 0x7E, 0x1C] (LoadPre 0x126377 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126377 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126377 15 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x126377 15 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x126377 0x45 (by decide) 7 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12637b [0x44, 0x01, 0xFD] (fun s => s.RIP = 0x12637b) (addR32R32Effect 0x12637b 3 5 15)
      [.gpr 5, .gpr 15] [] [.reg 5, .flags, .rip] :=
    (addR32R32Effect_footprint 0x12637b 3 5 15).toInstrSpec (add_r32_r32_rex_effect_step 0x12637b 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12637b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12637e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel32_effect_step 0x12637e 2 0x428) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126377 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126377 :=
  Rest.liftedBlock (rest_l126377 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126377 x hx)

theorem rest_l126384 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126384 bytes_l126384) (entryMap (live .l126384))
      7 0x126384 bytes_l126384 b_l126384 := by
  have f0 : InstrSpec 0x126384 [0x49, 0x8B, 0x36] (LoadPre 0x126384 (fun s => AddrMode.addr (.base 14 .none) s (0x126384 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x126384 6 (.base 14 .none))
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126384 6 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x126384 0x49 (by decide) 6 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126387 [0x4D, 0x8B, 0x66, 0x08] (LoadPre 0x126387 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126387 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126387 12 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x126387 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x126387 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12638b [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x12638b) (leaR64Effect 0x12638b 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12638b 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x12638b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126390 [0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x126390 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126390 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126390 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126390 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x126390 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x126398 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x126398) (movR64R64Effect 0x126398 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x126398 2 12).toInstrSpec (mov_r64_r64_effect_step 0x126398 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12639b [0x89, 0xE9] (fun s => s.RIP = 0x12639b) (movR32R32Effect 0x12639b 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12639b 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x12639b 0xe9 (by decide)) pre_rip
  have f6 : InstrSpec 0x12639d [0xE8, 0xAE, 0x18, 0x00, 0x00] (PushPre 0x12639d 5) (callEffect (fun _ => 0x127c50) 0x1263a2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12639d 0x127c50 0x1263a2).toInstrSpec (call_rel32_effect_step 0x12639d 0x18ae (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126387) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12638b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126390) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126398) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 60), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12639b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 62), (2, 60), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12639d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 62), (2, 60), (3, 3), (4, 64), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c50) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l126384 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126384 :=
  Rest.liftedBlock (rest_l126384 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126384 x hx)

theorem rest_l1263a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1263a2 bytes_l1263a2) (entryMap (live .l1263a2))
      3 0x1263a2 bytes_l1263a2 b_l1263a2 := by
  have f0 : InstrSpec 0x1263a2 [0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x1263a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1263a2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1263a2 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1263a2 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x1263a2 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1263a6 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x1263a6) (cmpR32Imm8Effect 0x1263a6 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1263a6 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1263a6 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263a6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263a9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1263a9 5 0x1c8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1263a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1263a2 :=
  Rest.liftedBlock (rest_l1263a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1263a2 x hx)

theorem rest_l1263af [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1263af bytes_l1263af) (entryMap (live .l1263af))
      7 0x1263af bytes_l1263af b_l1263af := by
  have f0 : InstrSpec 0x1263af [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1263af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1263af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263af 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1263af 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1263af 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1263b4 [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x1263b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1263b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263b4 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1263b4 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1263b4 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1263b9 [0x49, 0x89, 0x06] (StorePre 0x1263b9 3 (fun s => AddrMode.addr (.base 14 .none) s (0x1263b9 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1263b9 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1263b9 0 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1263b9 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1263bc [0x49, 0x89, 0x4E, 0x08] (StorePre 0x1263bc 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1263bc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1263bc 1 (.base 14 (.d8 0x8)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1263bc 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1263bc 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1263c0 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x1263c0 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1263c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1263c0 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1263c0 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1263c0 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1263c4 [0x48, 0x83, 0xF8, 0x3F] (fun s => s.RIP = 0x1263c4) (cmpR64Imm8Effect 0x1263c4 0 0x3f)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1263c4 0 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x1263c4 0x48 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263b9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263bc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263c0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263c4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263c8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel32_effect_step 0x1263c8 6 0x206) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1263af [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1263af :=
  Rest.liftedBlock (rest_l1263af code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1263af x hx)

theorem rest_l1263ce [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1263ce bytes_l1263ce) (entryMap (live .l1263ce))
      2 0x1263ce bytes_l1263ce b_l1263ce := by
  have f0 : InstrSpec 0x1263ce [0x41, 0xB8, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1263ce) (movR32Imm32Effect 0x1263ce 6 8 0x6)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x1263ce 6 8 0x6).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1263ce 0x41 0xb8 (by decide) (by decide) 0x6) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1263d4 0x217 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1263ce [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1263ce :=
  Rest.liftedBlock (rest_l1263ce code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1263ce x hx)

theorem rest_l1263d9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1263d9 bytes_l1263d9) (entryMap (live .l1263d9))
      17 0x1263d9 bytes_l1263d9 b_l1263d9 := by
  have f0 : InstrSpec 0x1263d9 [0x8B, 0x54, 0x24, 0x54] (LoadPre 0x1263d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x1263d9 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1263d9 2 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1263d9 2 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_low_effect_step 0x1263d9 2 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1263dd [0x89, 0x53, 0x34] (StorePre 0x1263dd 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x1263dd + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1263dd 2 (.base 3 (.d8 0x34)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1263dd 2 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x1263dd 2 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1263e0 [0x48, 0x8B, 0x54, 0x24, 0x4D] (LoadPre 0x1263e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x1263e0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263e0 2 (.sib 4 none 0 (.d8 0x4d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1263e0 2 (.sib 4 none 0 (.d8 0x4d))).toInstrSpec (mov_r64_m64_effect_step 0x1263e0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x4d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1263e5 [0x48, 0x89, 0x53, 0x2D] (StorePre 0x1263e5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x1263e5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1263e5 2 (.base 3 (.d8 0x2d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1263e5 2 (.base 3 (.d8 0x2d))).toInstrSpec (mov_m64_r64_effect_step 0x1263e5 0x48 (by decide) 2 (.base 3 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1263e9 [0x48, 0x8B, 0x54, 0x24, 0x45] (LoadPre 0x1263e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x1263e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263e9 2 (.sib 4 none 0 (.d8 0x45)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1263e9 2 (.sib 4 none 0 (.d8 0x45))).toInstrSpec (mov_r64_m64_effect_step 0x1263e9 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x45)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1263ee [0x48, 0x89, 0x53, 0x25] (StorePre 0x1263ee 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x1263ee + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1263ee 2 (.base 3 (.d8 0x25)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1263ee 2 (.base 3 (.d8 0x25))).toInstrSpec (mov_m64_r64_effect_step 0x1263ee 0x48 (by decide) 2 (.base 3 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1263f2 [0x48, 0x8B, 0x54, 0x24, 0x3D] (LoadPre 0x1263f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x1263f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263f2 2 (.sib 4 none 0 (.d8 0x3d)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1263f2 2 (.sib 4 none 0 (.d8 0x3d))).toInstrSpec (mov_r64_m64_effect_step 0x1263f2 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x3d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1263f7 [0x48, 0x89, 0x53, 0x1D] (StorePre 0x1263f7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x1263f7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1263f7 2 (.base 3 (.d8 0x1d)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1263f7 2 (.base 3 (.d8 0x1d))).toInstrSpec (mov_m64_r64_effect_step 0x1263f7 0x48 (by decide) 2 (.base 3 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1263fb [0x48, 0x8B, 0x54, 0x24, 0x35] (LoadPre 0x1263fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x1263fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1263fb 2 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1263fb 2 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (mov_r64_m64_effect_step 0x1263fb 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126400 [0x48, 0x89, 0x53, 0x15] (StorePre 0x126400 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x126400 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126400 2 (.base 3 (.d8 0x15)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126400 2 (.base 3 (.d8 0x15))).toInstrSpec (mov_m64_r64_effect_step 0x126400 0x48 (by decide) 2 (.base 3 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x126404 [0x48, 0x8B, 0x54, 0x24, 0x25] (LoadPre 0x126404 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x126404 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126404 2 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126404 2 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (mov_r64_m64_effect_step 0x126404 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x126409 [0x48, 0x8B, 0x74, 0x24, 0x2D] (LoadPre 0x126409 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x126409 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126409 6 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x126409 6 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (mov_r64_m64_effect_step 0x126409 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12640e [0x48, 0x89, 0x73, 0x0D] (StorePre 0x12640e 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x12640e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12640e 6 (.base 3 (.d8 0xd)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12640e 6 (.base 3 (.d8 0xd))).toInstrSpec (mov_m64_r64_effect_step 0x12640e 0x48 (by decide) 6 (.base 3 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x126412 [0x48, 0x89, 0x53, 0x05] (StorePre 0x126412 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x126412 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126412 2 (.base 3 (.d8 0x5)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126412 2 (.base 3 (.d8 0x5))).toInstrSpec (mov_m64_r64_effect_step 0x126412 0x48 (by decide) 2 (.base 3 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x126416 [0x89, 0x0B] (StorePre 0x126416 2 (fun s => AddrMode.addr (.base 3 .none) s (0x126416 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x126416 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126416 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x126416 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x126418 [0x88, 0x43, 0x04] (StorePre 0x126418 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x126418 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x126418 3 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x126418 3 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x126418 0 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263e0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263e5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263e9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263ee) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263f2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263f7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1263fb) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126400) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126404) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126409) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12640e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126412) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126416) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126418) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 68), (3, 3), (4, 4), (6, 70), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12641b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 76) (jmp_rel32_effect_step 0x12641b 0x142 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1263d9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1263d9 :=
  Rest.liftedBlock (rest_l1263d9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1263d9 x hx)

theorem rest_l126420 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126420 bytes_l126420) (entryMap (live .l126420))
      3 0x126420 bytes_l126420 b_l126420 := by
  have f0 : InstrSpec 0x126420 [0xC6, 0x43, 0x30, 0x02] (StorePre 0x126420 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126420 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x126420 (.base 3 (.d8 0x30)) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x126420 (.base 3 (.d8 0x30)) 0x2).toInstrSpec (mov_m8_imm8_effect_step 0x126420 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126424 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x126424 6 (fun s => AddrMode.addr (.base 3 .none) s (0x126424 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x126424 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x126424 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x126424 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126424) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12642a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x12642a 0x133 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126420 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126420 :=
  Rest.liftedBlock (rest_l126420 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126420 x hx)

theorem rest_l12642f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12642f bytes_l12642f) (entryMap (live .l12642f))
      17 0x12642f bytes_l12642f b_l12642f := by
  have f0 : InstrSpec 0x12642f [0x44, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x12642f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12642f + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12642f 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x12642f 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r32_m32_effect_step 0x12642f 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126434 [0x48, 0x8B, 0x54, 0x24, 0x34] (LoadPre 0x126434 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x126434 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126434 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x126434 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x126434 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126439 [0x48, 0x89, 0x54, 0x24, 0x14] (StorePre 0x126439 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x126439 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126439 2 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126439 2 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x126439 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x12643e [0x44, 0x8B, 0x74, 0x24, 0x3C] (LoadPre 0x12643e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x12643e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12643e 14 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x12643e 14 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_effect_step 0x12643e 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x126443 [0x4C, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x126443 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126443 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126443 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x126443 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x126443 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126448 [0x8B, 0x54, 0x24, 0x48] (LoadPre 0x126448 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126448 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126448 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126448 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x126448 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12644c [0x8B, 0x74, 0x24, 0x4C] (LoadPre 0x12644c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x12644c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12644c 6 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x12644c 6 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x12644c 6 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x126450 [0x0F, 0xB6, 0x7C, 0x24, 0x50] (LoadPre 0x126450 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126450 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x126450 5 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x126450 5 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x126450 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x126455 [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x51] (LoadPre 0x126455 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x126455 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x126455 6 9 (.sib 4 none 0 (.d8 0x51)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x126455 6 9 (.sib 4 none 0 (.d8 0x51))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x126455 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x51)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x12645b [0x66, 0x44, 0x89, 0x0C, 0x24] (StorePre 0x12645b 5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12645b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x12645b 5 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x12645b 5 9 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_rex_effect_step 0x12645b 0x44 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x126460 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x53] (LoadPre 0x126460 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x126460 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126460 6 9 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x126460 6 9 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x126460 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x126466 [0x44, 0x88, 0x4C, 0x24, 0x02] (StorePre 0x126466 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x126466 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x126466 5 9 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x126466 5 9 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x126466 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12646b [0x44, 0x8B, 0x4C, 0x24, 0x54] (LoadPre 0x12646b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x12646b + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12646b 9 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x12646b 9 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_effect_step 0x12646b 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x126470 [0x44, 0x89, 0x6C, 0x24, 0x08] (StorePre 0x126470 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126470 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126470 13 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x126470 13 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_effect_step 0x126470 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x126475 [0x89, 0x6C, 0x24, 0x0C] (StorePre 0x126475 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126475 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126475 5 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126475 5 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x126475 5 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x126479 [0x44, 0x89, 0x44, 0x24, 0x10] (StorePre 0x126479 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126479 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126479 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x126479 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x126479 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 53), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126434) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 53), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126439) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 53), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12643e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 53), (10, 10), (11, 11), (13, 13), (14, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126443) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 53), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126448) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (8, 53), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12644c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (8, 53), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126450) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126455) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (9, 68), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12645b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (9, 68), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126460) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (9, 71), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126466) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (9, 71), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12646b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (9, 74), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126470) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (9, 74), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126475) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (9, 74), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126479) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 64), (7, 66), (8, 53), (9, 74), (10, 10), (11, 11), (13, 13), (14, 58), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12647e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 79) (jmp_rel8_effect_step 0x12647e 0x78 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12642f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12642f :=
  Rest.liftedBlock (rest_l12642f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12642f x hx)

theorem rest_l126480 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126480 bytes_l126480) (entryMap (live .l126480))
      3 0x126480 bytes_l126480 b_l126480 := by
  have f0 : InstrSpec 0x126480 [0x83, 0xC1, 0xF6] (fun s => s.RIP = 0x126480) (addR32Imm8Effect 0x126480 3 1 0xf6)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32Imm8Effect_footprint 0x126480 3 1 0xf6).toInstrSpec (add_r32_imm8_effect_step 0x126480 0xc1 0xf6 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126483 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x126483) (cmpR32Imm8Effect 0x126483 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126483 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126483 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126483) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126486) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x126486 3 0x39) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126480 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126480 :=
  Rest.liftedBlock (rest_l126480 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126480 x hx)

theorem rest_l126488 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126488 bytes_l126488) (entryMap (live .l126488))
      14 0x126488 bytes_l126488 b_l126488 := by
  have f0 : InstrSpec 0x126488 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x126488 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126488 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126488 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x126488 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x126488 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12648d [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x12648d (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x12648d + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12648d 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x12648d 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x12648d 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126491 [0xC6, 0x44, 0x24, 0x08, 0x11] (StorePre 0x126491 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126491 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x126491 (.sib 4 none 0 (.d8 0x8)) 0x11)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x126491 (.sib 4 none 0 (.d8 0x8)) 0x11).toInstrSpec (mov_m8_imm8_effect_step 0x126491 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x11) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x126496 [0xC6, 0x44, 0x24, 0x0C, 0xFF] (StorePre 0x126496 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126496 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x126496 (.sib 4 none 0 (.d8 0xc)) 0xff)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x126496 (.sib 4 none 0 (.d8 0xc)) 0xff).toInstrSpec (mov_m8_imm8_effect_step 0x126496 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide) 0xff) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12649b [0x88, 0x44, 0x24, 0x14] (StorePre 0x12649b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x12649b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12649b 4 0 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x12649b 4 0 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m8_r8_effect_step 0x12649b 0 (by decide) (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12649f [0x44, 0x88, 0x5C, 0x24, 0x15] (StorePre 0x12649f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x12649f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x12649f 5 11 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x12649f 5 11 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_rex_effect_step 0x12649f 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1264a4 [0x66, 0x44, 0x89, 0x54, 0x24, 0x16] (StorePre 0x1264a4 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x1264a4 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1264a4 6 10 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1264a4 6 10 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1264a4 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1264aa [0x41, 0x89, 0xCA] (fun s => s.RIP = 0x1264aa) (movR32R32Effect 0x1264aa 3 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1264aa 3 10 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1264aa 0x41 0xca (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1264ad [0x89, 0xC8] (fun s => s.RIP = 0x1264ad) (movR32R32Effect 0x1264ad 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1264ad 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1264ad 0xc8 (by decide)) pre_rip
  have f9 : InstrSpec 0x1264af [0x41, 0x89, 0xCB] (fun s => s.RIP = 0x1264af) (movR32R32Effect 0x1264af 3 11 1)
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1264af 3 11 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1264af 0x41 0xcb (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1264b2 [0x41, 0xC1, 0xEB, 0x08] (fun s => s.RIP = 0x1264b2) (shrR32Effect 0x1264b2 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x1264b2 4 11 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1264b2 0x41 0xeb 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1264b6 [0x41, 0xC1, 0xEA, 0x10] (fun s => s.RIP = 0x1264b6) (shrR32Effect 0x1264b6 4 10 16)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x1264b6 4 10 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1264b6 0x41 0xea 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1264ba [0x44, 0x89, 0x6C, 0x24, 0x18] (StorePre 0x1264ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1264ba + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1264ba 13 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1264ba 13 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x1264ba 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12648d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126491) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126496) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12649b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12649f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264a4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264aa) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f7 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 61), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264ad) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 61), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264af) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 61), (11, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264b2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 61), (11, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264b6) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 69), (11, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264ba) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 63), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 69), (11, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264bf) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 72) (jmp_rel8_effect_step 0x1264bf 0x32 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126488 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126488 :=
  Rest.liftedBlock (rest_l126488 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126488 x hx)

theorem rest_l1264c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1264c1 bytes_l1264c1) (entryMap (live .l1264c1))
      12 0x1264c1 bytes_l1264c1 b_l1264c1 := by
  have f0 : InstrSpec 0x1264c1 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1264c1 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1264c1 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1264c1 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1264c1 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1264c1 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1264c6 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x1264c6 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1264c6 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1264c6 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x1264c6 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1264c6 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1264ca [0xC6, 0x44, 0x24, 0x08, 0x07] (StorePre 0x1264ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1264ca + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x1264ca (.sib 4 none 0 (.d8 0x8)) 0x7)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1264ca (.sib 4 none 0 (.d8 0x8)) 0x7).toInstrSpec (mov_m8_imm8_effect_step 0x1264ca (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x7) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1264cf [0x88, 0x44, 0x24, 0x0C] (StorePre 0x1264cf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1264cf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1264cf 4 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1264cf 4 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_effect_step 0x1264cf 0 (by decide) (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1264d3 [0x44, 0x88, 0x5C, 0x24, 0x0D] (StorePre 0x1264d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1264d3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1264d3 5 11 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1264d3 5 11 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1264d3 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1264d8 [0x66, 0x44, 0x89, 0x54, 0x24, 0x0E] (StorePre 0x1264d8 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1264d8 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1264d8 6 10 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1264d8 6 10 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1264d8 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1264de [0x41, 0x89, 0xCA] (fun s => s.RIP = 0x1264de) (movR32R32Effect 0x1264de 3 10 1)
      [.gpr 1] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1264de 3 10 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1264de 0x41 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1264e1 [0x89, 0xC8] (fun s => s.RIP = 0x1264e1) (movR32R32Effect 0x1264e1 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1264e1 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x1264e1 0xc8 (by decide)) pre_rip
  have f8 : InstrSpec 0x1264e3 [0x41, 0x89, 0xCB] (fun s => s.RIP = 0x1264e3) (movR32R32Effect 0x1264e3 3 11 1)
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1264e3 3 11 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1264e3 0x41 0xcb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1264e6 [0x41, 0xC1, 0xEB, 0x08] (fun s => s.RIP = 0x1264e6) (shrR32Effect 0x1264e6 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x1264e6 4 11 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1264e6 0x41 0xeb 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1264ea [0x41, 0xC1, 0xEA, 0x10] (fun s => s.RIP = 0x1264ea) (shrR32Effect 0x1264ea 4 10 16)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x1264ea 4 10 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1264ea 0x41 0xea 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1264ee [0x44, 0x89, 0x6C, 0x24, 0x10] (StorePre 0x1264ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1264ee + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1264ee 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1264ee 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x1264ee 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264c6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264d3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264d8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264de) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 60), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264e1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 60), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264e3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 62), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 60), (11, 64), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264e6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 60), (11, 66), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264ea) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 68), (11, 66), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264ee) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 62), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 68), (11, 66), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264f3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l1264c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1264c1 :=
  Rest.liftedBlock (rest_l1264c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1264c1 x hx)

theorem rest_l1264f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1264f3 bytes_l1264f3) (entryMap (live .l1264f3))
      1 0x1264f3 bytes_l1264f3 b_l1264f3 := by
  have f0 : InstrSpec 0x1264f3 [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1264f3) (movR32Imm32Effect 0x1264f3 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1264f3 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1264f3 0xb9 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1264f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1264f3 :=
  Rest.liftedBlock (rest_l1264f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1264f3 x hx)

theorem rest_l1264f8_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x1264f8 bytes_l1264f8) [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x126547 bytes_l1264f8_1 b_l1264f8_1 := by
  have f20 : InstrSpec 0x126547 [0x89, 0x73, 0x2C] (StorePre 0x126547 3 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x126547 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126547 6 (.base 3 (.d8 0x2c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126547 6 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m32_r32_low_effect_step 0x126547 6 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x12654a [0x40, 0x88, 0x7B, 0x30] (StorePre 0x12654a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12654a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12654a 4 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x12654a 4 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m8_r8_rex_effect_step 0x12654a 0x40 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x12654e [0x0F, 0xB7, 0x04, 0x24] (LoadPre 0x12654e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12654e + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12654e 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x12654e 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12654e 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x126552 [0x66, 0x89, 0x43, 0x31] (StorePre 0x126552 4 (fun s => AddrMode.addr (.base 3 (.d8 0x31)) s (0x126552 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x126552 4 0 (.base 3 (.d8 0x31)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x126552 4 0 (.base 3 (.d8 0x31))).toInstrSpec (mov_m16_r16_effect_step 0x126552 0 (.base 3 (.d8 0x31)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x126556 [0x0F, 0xB6, 0x44, 0x24, 0x02] (LoadPre 0x126556 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x126556 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x126556 5 0 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x126556 5 0 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m8_effect_step 0x126556 0 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x12655b [0x88, 0x43, 0x33] (StorePre 0x12655b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x33)) s (0x12655b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12655b 3 0 (.base 3 (.d8 0x33)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x12655b 3 0 (.base 3 (.d8 0x33))).toInstrSpec (mov_m8_r8_effect_step 0x12655b 0 (by decide) (.base 3 (.d8 0x33)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x12655e [0x44, 0x89, 0x4B, 0x34] (StorePre 0x12655e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x12655e + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12655e 9 (.base 3 (.d8 0x34)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x12655e 9 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_effect_step 0x12655e 0x44 (by decide) 1 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12654a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12654e) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126552) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 84), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126556) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12655b) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12655e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126562) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 91) (by decide) rfl

theorem rest_l1264f8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1264f8 bytes_l1264f8) (entryMap (live .l1264f8))
      27 0x1264f8 bytes_l1264f8 b_l1264f8 := by
  have f0 : InstrSpec 0x1264f8 [0x41, 0xC1, 0xE2, 0x10] (fun s => s.RIP = 0x1264f8) (shlR32Effect 0x1264f8 4 10 16)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x1264f8 4 10 16).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1264f8 0x41 0xe2 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1264fc [0x45, 0x0F, 0xB6, 0xC3] (fun s => s.RIP = 0x1264fc) (movzxR32R8Effect 0x1264fc 4 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movzxR32R8Effect_footprint 0x1264fc 4 8 11).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1264fc 0x45 (by decide) 0xc3 (by decide)) pre_rip
  have f2 : InstrSpec 0x126500 [0x41, 0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x126500) (shlR32Effect 0x126500 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR32Effect_footprint 0x126500 4 8 8).toInstrSpec (shl_r32_imm8_rex_effect_step 0x126500 0x41 0xe0 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126504 [0x45, 0x09, 0xD0] (fun s => s.RIP = 0x126504) (orR32R32Effect 0x126504 3 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (orR32R32Effect_footprint 0x126504 3 8 10).toInstrSpec (or_r32_r32_rex_effect_step 0x126504 0x45 0xd0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x126507 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x126507) (movzxR32R8Effect 0x126507 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x126507 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x126507 0xc0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12650a [0x44, 0x09, 0xC0] (fun s => s.RIP = 0x12650a) (orR32R32Effect 0x12650a 3 0 8)
      [.gpr 0, .gpr 8] [] [.reg 0, .flags, .rip] :=
    (orR32R32Effect_footprint 0x12650a 3 0 8).toInstrSpec (or_r32_r32_rex_effect_step 0x12650a 0x44 0xc0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12650d [0x44, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x12650d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12650d + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12650d 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x12650d 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x12650d 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x126512 [0x44, 0x89, 0x44, 0x24, 0x78] (StorePre 0x126512 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126512 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126512 8 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x126512 8 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m32_r32_effect_step 0x126512 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126517 [0x4C, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x126517 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126517 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126517 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x126517 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x126517 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x12651c [0x4C, 0x8B, 0x5C, 0x24, 0x10] (LoadPre 0x12651c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12651c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12651c 11 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x12651c 11 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12651c 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x126521 [0x4C, 0x89, 0x5C, 0x24, 0x70] (StorePre 0x126521 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126521 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126521 11 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126521 11 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x126521 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x126526 [0x4C, 0x89, 0x54, 0x24, 0x68] (StorePre 0x126526 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126526 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126526 10 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126526 10 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x126526 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12652b [0x44, 0x89, 0x43, 0x18] (StorePre 0x12652b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x12652b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12652b 8 (.base 3 (.d8 0x18)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x12652b 8 (.base 3 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x12652b 0x44 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x12652f [0x4C, 0x89, 0x5B, 0x10] (StorePre 0x12652f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12652f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12652f 11 (.base 3 (.d8 0x10)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12652f 11 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12652f 0x4c (by decide) 3 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x126533 [0x4C, 0x89, 0x53, 0x08] (StorePre 0x126533 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126533 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126533 10 (.base 3 (.d8 0x8)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126533 10 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126533 0x4c (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x126537 [0x89, 0x0B] (StorePre 0x126537 2 (fun s => AddrMode.addr (.base 3 .none) s (0x126537 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x126537 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126537 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x126537 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x126539 [0x89, 0x43, 0x04] (StorePre 0x126539 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x126539 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126539 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126539 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x126539 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x12653c [0x44, 0x89, 0x73, 0x1C] (StorePre 0x12653c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x12653c + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12653c 14 (.base 3 (.d8 0x1c)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x12653c 14 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m32_r32_effect_step 0x12653c 0x44 (by decide) 6 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x126540 [0x4C, 0x89, 0x7B, 0x20] (StorePre 0x126540 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126540 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126540 15 (.base 3 (.d8 0x20)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126540 15 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x126540 0x4c (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x126544 [0x89, 0x53, 0x28] (StorePre 0x126544 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126544 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126544 2 (.base 3 (.d8 0x28)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126544 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_m32_r32_low_effect_step 0x126544 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 53), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1264fc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 53), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126500) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 53), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126504) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (10, 53), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126507) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (10, 53), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12650a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (10, 53), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12650d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 53), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126512) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 53), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126517) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12651c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126521) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126526) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12652b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12652f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126533) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126537) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126539) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12653c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126540) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126544) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 65), (9, 9), (10, 68), (11, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126547) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1264f8_1 code

theorem block_l1264f8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1264f8 :=
  Rest.liftedBlock (rest_l1264f8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1264f8 x hx)

theorem rest_l126562 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126562 bytes_l126562) (entryMap (live .l126562))
      9 0x126562 bytes_l126562 b_l126562 := by
  have f0 : InstrSpec 0x126562 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x126562) (movR64R64Effect 0x126562 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x126562 0 3).toInstrSpec (mov_r64_r64_effect_step 0x126562 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126565 [0x48, 0x81, 0xC4, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126565) (addR64Imm32Effect 0x126565 4 0xb8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x126565 4 0xb8).toInstrSpec (add_r64_imm32_effect_step 0x126565 0x48 0xc4 0xb8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12656c [0x5B] (PopPre 0x12656c) (popR64Effect 0x12656c 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12656c 1 3).toInstrSpec (pop_r64_effect_step 0x12656c 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12656d [0x41, 0x5C] (PopPre 0x12656d) (popR64Effect 0x12656d 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12656d 2 12).toInstrSpec (pop_r64_rex_effect_step 0x12656d 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x12656f [0x41, 0x5D] (PopPre 0x12656f) (popR64Effect 0x12656f 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12656f 2 13).toInstrSpec (pop_r64_rex_effect_step 0x12656f 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x126571 [0x41, 0x5E] (PopPre 0x126571) (popR64Effect 0x126571 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126571 2 14).toInstrSpec (pop_r64_rex_effect_step 0x126571 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x126573 [0x41, 0x5F] (PopPre 0x126573) (popR64Effect 0x126573 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126573 2 15).toInstrSpec (pop_r64_rex_effect_step 0x126573 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x126575 [0x5D] (PopPre 0x126575) (popR64Effect 0x126575 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x126575 1 5).toInstrSpec (pop_r64_effect_step 0x126575 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x126576 [0xC3] (RetPre 0x126576) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x126576).toInstrSpec (ret_effect_step 0x126576) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126565) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12656c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12656d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12656f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126571) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126573) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126575) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126576) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l126562 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126562 :=
  Rest.liftedBlock (rest_l126562 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126562 x hx)

theorem rest_l126577 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126577 bytes_l126577) (entryMap (live .l126577))
      19 0x126577 bytes_l126577 b_l126577 := by
  have f0 : InstrSpec 0x126577 [0x8B, 0x44, 0x24, 0x24] (LoadPre 0x126577 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x126577 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126577 0 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x126577 0 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x126577 0 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12657b [0x4C, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x12657b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12657b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12657b 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x12657b 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x12657b 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126580 [0x4C, 0x8B, 0x5C, 0x24, 0x30] (LoadPre 0x126580 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126580 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126580 11 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x126580 11 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x126580 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126585 [0x44, 0x8B, 0x54, 0x24, 0x38] (LoadPre 0x126585 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126585 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126585 10 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x126585 10 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r32_m32_effect_step 0x126585 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12658a [0x48, 0x8B, 0x54, 0x24, 0x3C] (LoadPre 0x12658a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x12658a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12658a 2 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12658a 2 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r64_m64_effect_step 0x12658a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12658f [0x48, 0x89, 0x54, 0x24, 0x58] (StorePre 0x12658f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12658f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12658f 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12658f 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x12658f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x126594 [0x8B, 0x54, 0x24, 0x44] (LoadPre 0x126594 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x126594 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126594 2 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x126594 2 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x126594 2 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x126598 [0x89, 0x54, 0x24, 0x60] (StorePre 0x126598 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126598 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126598 2 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126598 2 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m32_r32_low_effect_step 0x126598 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12659c [0x8B, 0x54, 0x24, 0x48] (LoadPre 0x12659c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12659c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12659c 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x12659c 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x12659c 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1265a0 [0x8B, 0x74, 0x24, 0x4C] (LoadPre 0x1265a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1265a0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1265a0 6 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x1265a0 6 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x1265a0 6 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1265a4 [0x0F, 0xB6, 0x7C, 0x24, 0x50] (LoadPre 0x1265a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1265a4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1265a4 5 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1265a4 5 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x1265a4 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1265a9 [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x51] (LoadPre 0x1265a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x1265a9 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1265a9 6 9 (.sib 4 none 0 (.d8 0x51)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x1265a9 6 9 (.sib 4 none 0 (.d8 0x51))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1265a9 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x51)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1265af [0x66, 0x44, 0x89, 0x4C, 0x24, 0x04] (StorePre 0x1265af 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1265af + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1265af 6 9 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1265af 6 9 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1265af 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1265b5 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x53] (LoadPre 0x1265b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x1265b5 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1265b5 6 9 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1265b5 6 9 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1265b5 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1265bb [0x44, 0x88, 0x4C, 0x24, 0x06] (StorePre 0x1265bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1265bb + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1265bb 5 9 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1265bb 5 9 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1265bb 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1265c0 [0x44, 0x8B, 0x4C, 0x24, 0x54] (LoadPre 0x1265c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x1265c0 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1265c0 9 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x1265c0 9 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_effect_step 0x1265c0 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x1265c5 [0x49, 0xBE, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x1265c5) (movR64Imm64Effect 0x1265c5 14 0xffffffff00000000)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x1265c5 14 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x1265c5 0x49 0xbe (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f17 : InstrSpec 0x1265cf [0x4D, 0x21, 0xDE] (fun s => s.RIP = 0x1265cf) (andR64R64Effect 0x1265cf 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1265cf 14 11).toInstrSpec (and_r64_r64_effect_step 0x1265cf 0x4d 0xde (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12657b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (8, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126580) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (8, 55), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126585) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12658a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 61), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12658f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 1), (2, 61), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126594) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 64), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126598) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 1), (2, 64), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12659c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265a0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (8, 55), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265a4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265a9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 73), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265af) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 73), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265b5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 76), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265bb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 76), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265c0) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 79), (10, 59), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265c5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 79), (10, 59), (11, 57), (14, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265cf) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f17 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 79), (10, 59), (11, 57), (14, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265d2) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 85) (jmp_rel8_effect_step 0x1265d2 0x2a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126577 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126577 :=
  Rest.liftedBlock (rest_l126577 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126577 x hx)

theorem rest_l1265d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1265d4 bytes_l1265d4) (entryMap (live .l1265d4))
      5 0x1265d4 bytes_l1265d4 b_l1265d4 := by
  have f0 : InstrSpec 0x1265d4 [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x1265d4) (incR64Effect 0x1265d4 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x1265d4 0).toInstrSpec (inc_r64_effect_step 0x1265d4 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1265d7 [0x49, 0x89, 0x46, 0x10] (StorePre 0x1265d7 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1265d7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1265d7 0 (.base 14 (.d8 0x10)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1265d7 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1265d7 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1265db [0x45, 0x8B, 0x7E, 0x18] (LoadPre 0x1265db (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1265db + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1265db 15 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x1265db 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x1265db 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1265df [0x44, 0x39, 0xFD] (fun s => s.RIP = 0x1265df) (cmpR32R32Effect 0x1265df 3 5 15)
      [.gpr 5, .gpr 15] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x1265df 3 5 15).toInstrSpec (cmp_r32_r32_rex_effect_step 0x1265df 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265d7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265df) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265e2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x1265e2 6 0x7f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1265d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1265d4 :=
  Rest.liftedBlock (rest_l1265d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1265d4 x hx)

theorem rest_l1265e4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1265e4 bytes_l1265e4) (entryMap (live .l1265e4))
      3 0x1265e4 bytes_l1265e4 b_l1265e4 := by
  have f0 : InstrSpec 0x1265e4 [0x45, 0x8D, 0x47, 0x01] (fun s => s.RIP = 0x1265e4) (leaR32Effect 0x1265e4 4 8 (.base 15 (.d8 0x1)))
      [.gpr 15] [] [.reg 8, .rip] :=
    (leaR32Effect_footprint 0x1265e4 4 8 (.base 15 (.d8 0x1))).toInstrSpec (lea_r32_rex_effect_step 0x1265e4 0x45 (by decide) 0 (.base 15 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1265e8 [0x49, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x1265e8) (shlR64Effect 0x1265e8 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x1265e8 4 8 32).toInstrSpec (shl_r64_imm8_effect_step 0x1265e8 0x49 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1265ec [0x49, 0x83, 0xC8, 0x03] (fun s => s.RIP = 0x1265ec) (orR64Imm8Effect 0x1265ec 8 0x3)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x1265ec 8 0x3).toInstrSpec (or_r64_imm8_effect_step 0x1265ec 0x49 0xc8 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265e8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265f0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l1265e4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1265e4 :=
  Rest.liftedBlock (rest_l1265e4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1265e4 x hx)

theorem rest_l1265f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1265f0 bytes_l1265f0) (entryMap (live .l1265f0))
      4 0x1265f0 bytes_l1265f0 b_l1265f0 := by
  have f0 : InstrSpec 0x1265f0 [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1265f0) (movR32Imm32Effect 0x1265f0 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1265f0 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1265f0 0xb9 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x1265f5 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x1265f5) (xorR32R32Effect 0x1265f5 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1265f5 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1265f5 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1265f8 [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x1265f8) (movR32R32Effect 0x1265f8 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1265f8 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1265f8 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1265fb [0x45, 0x89, 0xFB] (fun s => s.RIP = 0x1265fb) (movR32R32Effect 0x1265fb 3 11 15)
      [.gpr 15] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1265fb 3 11 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1265fb 0x45 0xfb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265f8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265fb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 59), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1265fe) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l1265f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1265f0 :=
  Rest.liftedBlock (rest_l1265f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1265f0 x hx)

theorem rest_l1265fe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1265fe bytes_l1265fe) (entryMap (live .l1265fe))
      20 0x1265fe bytes_l1265fe b_l1265fe := by
  have f0 : InstrSpec 0x1265fe [0x45, 0x89, 0xDC] (fun s => s.RIP = 0x1265fe) (movR32R32Effect 0x1265fe 3 12 11)
      [.gpr 11] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x1265fe 3 12 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x1265fe 0x45 0xdc (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x126601 [0x4D, 0x09, 0xF4] (fun s => s.RIP = 0x126601) (orR64R64Effect 0x126601 12 14)
      [.gpr 12, .gpr 14] [] [.reg 12, .flags, .rip] :=
    (orR64R64Effect_footprint 0x126601 12 14).toInstrSpec (or_r64_r64_effect_step 0x126601 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126604 [0x44, 0x8B, 0x5C, 0x24, 0x60] (LoadPre 0x126604 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126604 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126604 11 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x126604 11 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r32_m32_effect_step 0x126604 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x126609 [0x44, 0x89, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x126609 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126609 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x126609 11 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x126609 11 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m32_r32_effect_step 0x126609 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x126611 [0x4C, 0x8B, 0x74, 0x24, 0x58] (LoadPre 0x126611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126611 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126611 14 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x126611 14 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x126611 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x126616 [0x0F, 0xB7, 0x6C, 0x24, 0x04] (LoadPre 0x126616 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x126616 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x126616 5 5 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M16Effect_footprint 0x126616 5 5 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (movzx_r32_m16_effect_step 0x126616 5 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12661b [0x66, 0x89, 0x2C, 0x24] (StorePre 0x12661b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12661b + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x12661b 4 5 (.sib 4 none 0 .none))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x12661b 4 5 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_effect_step 0x12661b 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12661f [0x0F, 0xB6, 0x6C, 0x24, 0x06] (LoadPre 0x12661f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x12661f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12661f 5 5 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x12661f 5 5 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (movzx_r32_m8_effect_step 0x12661f 5 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x126624 [0x40, 0x88, 0x6C, 0x24, 0x02] (StorePre 0x126624 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x126624 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x126624 5 5 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x126624 5 5 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x126624 0x40 (by decide) 5 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x126629 [0x4C, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x126629 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x126629 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126629 14 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126629 14 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x126629 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x126631 [0x44, 0x89, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x126631 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126631 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x126631 11 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x126631 11 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m32_r32_effect_step 0x126631 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x126639 [0x44, 0x89, 0x54, 0x24, 0x18] (StorePre 0x126639 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126639 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x126639 10 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x126639 10 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x126639 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12663e [0x4C, 0x8B, 0xBC, 0x24, 0x8C, 0x00, 0x00, 0x00] (LoadPre 0x12663e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x12663e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12663e 15 (.sib 4 none 0 (.d32 0x8c)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x12663e 15 (.sib 4 none 0 (.d32 0x8c))).toInstrSpec (mov_r64_m64_effect_step 0x12663e 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x8c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x126646 [0x41, 0x89, 0xC3] (fun s => s.RIP = 0x126646) (movR32R32Effect 0x126646 3 11 0)
      [.gpr 0] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x126646 3 11 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x126646 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x126649 [0x41, 0xC1, 0xEB, 0x08] (fun s => s.RIP = 0x126649) (shrR32Effect 0x126649 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x126649 4 11 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x126649 0x41 0xeb 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x12664d [0x41, 0x89, 0xC2] (fun s => s.RIP = 0x12664d) (movR32R32Effect 0x12664d 3 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x12664d 3 10 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x12664d 0x41 0xc2 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x126650 [0x41, 0xC1, 0xEA, 0x10] (fun s => s.RIP = 0x126650) (shrR32Effect 0x126650 4 10 16)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x126650 4 10 16).toInstrSpec (shr_r32_imm8_rex_effect_step 0x126650 0x41 0xea 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x126654 [0x4C, 0x89, 0x44, 0x24, 0x08] (StorePre 0x126654 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126654 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126654 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126654 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126654 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x126659 [0x4C, 0x89, 0x64, 0x24, 0x10] (StorePre 0x126659 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126659 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126659 12 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126659 12 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x126659 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126601) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126604) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126609) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126611) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126616) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12661b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12661f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126624) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126629) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126631) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126639) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12663e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 55), (14, 60), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126646) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 73), (12, 55), (14, 60), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126649) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 75), (12, 55), (14, 60), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12664d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 77), (11, 75), (12, 55), (14, 60), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126650) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 79), (11, 75), (12, 55), (14, 60), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126654) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 79), (11, 75), (12, 55), (14, 60), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126659) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 79), (11, 75), (12, 55), (14, 60), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12665e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 83) (jmp_rel32_effect_step 0x12665e 0xfffffe95 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1265fe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1265fe :=
  Rest.liftedBlock (rest_l1265fe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1265fe x hx)

theorem rest_l126663 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126663 bytes_l126663) (entryMap (live .l126663))
      4 0x126663 bytes_l126663 b_l126663 := by
  have f0 : InstrSpec 0x126663 [0x41, 0x89, 0x6E, 0x18] (StorePre 0x126663 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126663 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126663 5 (.base 14 (.d8 0x18)))
      [.gpr 5, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x126663 5 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x126663 0x41 (by decide) 5 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x126667 [0x48, 0x8D, 0x7C, 0x24, 0x20] (fun s => s.RIP = 0x126667) (leaR64Effect 0x126667 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x126667 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x126667 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12666c [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x12666c) (movR64R64Effect 0x12666c 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12666c 6 14).toInstrSpec (mov_r64_r64_effect_step 0x12666c 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12666f [0xE8, 0x6C, 0xE4, 0xFF, 0xFF] (PushPre 0x12666f 5) (callEffect (fun _ => 0x124ae0) 0x126674)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12666f 0x124ae0 0x126674).toInstrSpec (call_rel32_effect_step 0x12666f 0xffffe46c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126667) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12666c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12666f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ae0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 60) (by decide) (by decide) rfl rfl

theorem block_l126663 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126663 :=
  Rest.liftedBlock (rest_l126663 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126663 x hx)

theorem rest_l126674 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126674 bytes_l126674) (entryMap (live .l126674))
      17 0x126674 bytes_l126674 b_l126674 := by
  have f0 : InstrSpec 0x126674 [0x45, 0x8B, 0x5E, 0x18] (LoadPre 0x126674 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126674 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126674 11 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x126674 11 (.base 14 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x126674 0x45 (by decide) 3 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x126678 [0x41, 0x8B, 0x46, 0x1C] (LoadPre 0x126678 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126678 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126678 0 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x126678 0 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x126678 0x41 (by decide) 0 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12667c [0x41, 0x29, 0xC3] (fun s => s.RIP = 0x12667c) (subR32R32Effect 0x12667c 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12667c 3 11 0).toInstrSpec (sub_r32_r32_rex_effect_step 0x12667c 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12667f [0x0F, 0x96, 0xC2] (fun s => s.RIP = 0x12667f) (atFlags (condHolds 6) (setccR8Effect 0x12667f 3 2))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 2, .rip] :=
    (setccR8Effect_footprint 0x12667f 3 2 6).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x12667f 6 0xc2 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x126682 [0x48, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x126682 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126682 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126682 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126682 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x126682 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12668a [0x49, 0x89, 0x0E] (StorePre 0x12668a 3 (fun s => AddrMode.addr (.base 14 .none) s (0x12668a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12668a 1 (.base 14 .none))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x12668a 1 (.base 14 .none)).toInstrSpec (mov_m64_r64_effect_step 0x12668a 0x49 (by decide) 1 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x12668d [0x4D, 0x89, 0x66, 0x08] (StorePre 0x12668d 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12668d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12668d 12 (.base 14 (.d8 0x8)))
      [.gpr 12, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x12668d 12 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12668d 0x4d (by decide) 4 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x126691 [0x45, 0x89, 0x7E, 0x18] (StorePre 0x126691 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126691 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126691 15 (.base 14 (.d8 0x18)))
      [.gpr 15, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x126691 15 (.base 14 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x126691 0x45 (by decide) 7 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x126695 [0x49, 0x8B, 0x4E, 0x10] (LoadPre 0x126695 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126695 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126695 1 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x126695 1 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x126695 0x49 (by decide) 1 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x126699 [0x48, 0x83, 0xF9, 0x01] (fun s => s.RIP = 0x126699) (cmpR64Imm8Effect 0x126699 1 0x1)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x126699 1 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x126699 0x48 0xf9 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12669d [0x48, 0x83, 0xD1, 0xFF] (fun s => s.RIP = 0x12669d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12669d 1 0xff))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x12669d 1 0xff).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x12669d 0x48 0xd1 0xff c (by decide) (by decide) (by decide))) pre_rip
  have f11 : InstrSpec 0x1266a1 [0x49, 0x89, 0x4E, 0x10] (StorePre 0x1266a1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1266a1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1266a1 1 (.base 14 (.d8 0x10)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x1266a1 1 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1266a1 0x49 (by decide) 1 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1266a5 [0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x1266a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1266a5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266a5 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1266a5 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x1266a5 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1266a9 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x1266a9) (cmpR32Imm8Effect 0x1266a9 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1266a9 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1266a9 0xf9 0x2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1266ac [0x40, 0x0F, 0x95, 0xC6] (fun s => s.RIP = 0x1266ac) (atFlags (condHolds 5) (setccR8Effect 0x1266ac 4 6))
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (setccR8Effect_footprint 0x1266ac 4 6 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1266ac 5 0x40 (by decide) 0xc6 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x1266b0 [0x40, 0x08, 0xD6] (fun s => s.RIP = 0x1266b0) (orR8R8Effect 0x1266b0 3 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (orR8R8Effect_footprint 0x1266b0 3 6 2).toInstrSpec (or_r8_r8_rex_effect_step 0x1266b0 0x40 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126678) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12667c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 59) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12667f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126682) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 63), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12668a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 63), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12668d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 63), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126691) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 63), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126695) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 68), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126699) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 55), (1, 68), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12669d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 55), (1, 72), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266a1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 72), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266a5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 75), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266a9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 75), (2, 61), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266ac) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 75), (2, 61), (3, 3), (4, 4), (6, 79), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266b0) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 55), (1, 75), (2, 61), (3, 3), (4, 4), (6, 81), (7, 7), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266b3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 84) (jcc_rel32_effect_step 0x1266b3 4 0xbf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l126674 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126674 :=
  Rest.liftedBlock (rest_l126674 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126674 x hx)

theorem rest_l1266b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1266b9 bytes_l1266b9) (entryMap (live .l1266b9))
      17 0x1266b9 bytes_l1266b9 b_l1266b9 := by
  have f0 : InstrSpec 0x1266b9 [0x8B, 0x44, 0x24, 0x24] (LoadPre 0x1266b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1266b9 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266b9 0 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1266b9 0 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x1266b9 0 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1266bd [0x4C, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1266bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1266bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1266bd 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1266bd 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1266bd 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1266c2 [0x4C, 0x8B, 0x5C, 0x24, 0x30] (LoadPre 0x1266c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1266c2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1266c2 11 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1266c2 11 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1266c2 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1266c7 [0x44, 0x8B, 0x54, 0x24, 0x38] (LoadPre 0x1266c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1266c7 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1266c7 10 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x1266c7 10 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r32_m32_effect_step 0x1266c7 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1266cc [0x48, 0x8B, 0x54, 0x24, 0x3C] (LoadPre 0x1266cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1266cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1266cc 2 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1266cc 2 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r64_m64_effect_step 0x1266cc 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1266d1 [0x48, 0x89, 0x54, 0x24, 0x58] (StorePre 0x1266d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1266d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1266d1 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1266d1 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1266d1 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1266d6 [0x8B, 0x54, 0x24, 0x44] (LoadPre 0x1266d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1266d6 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266d6 2 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1266d6 2 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x1266d6 2 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1266da [0x89, 0x54, 0x24, 0x60] (StorePre 0x1266da 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1266da + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1266da 2 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1266da 2 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m32_r32_low_effect_step 0x1266da 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1266de [0x8B, 0x54, 0x24, 0x48] (LoadPre 0x1266de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1266de + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266de 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1266de 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x1266de 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1266e2 [0x8B, 0x74, 0x24, 0x4C] (LoadPre 0x1266e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1266e2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1266e2 6 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x1266e2 6 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x1266e2 6 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1266e6 [0x0F, 0xB6, 0x7C, 0x24, 0x50] (LoadPre 0x1266e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1266e6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1266e6 5 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x1266e6 5 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x1266e6 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1266eb [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x51] (LoadPre 0x1266eb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x51)) s (0x1266eb + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1266eb 6 9 (.sib 4 none 0 (.d8 0x51)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x1266eb 6 9 (.sib 4 none 0 (.d8 0x51))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1266eb 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x51)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1266f1 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x04] (StorePre 0x1266f1 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1266f1 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1266f1 6 9 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1266f1 6 9 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1266f1 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1266f7 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x53] (LoadPre 0x1266f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x1266f7 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1266f7 6 9 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1266f7 6 9 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1266f7 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1266fd [0x44, 0x88, 0x4C, 0x24, 0x06] (StorePre 0x1266fd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1266fd + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1266fd 5 9 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1266fd 5 9 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1266fd 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x126702 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x126702) (cmpR32Imm8Effect 0x126702 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x126702 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x126702 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266bd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (8, 55), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266c2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (8, 55), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266c7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266cc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 61), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266d1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 1), (2, 61), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266d6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 64), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266da) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 1), (2, 64), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266de) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (8, 55), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266e2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (8, 55), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266e6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266eb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 73), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266f1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 73), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266f7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 76), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1266fd) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 76), (10, 59), (11, 57), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126702) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 1), (2, 67), (3, 3), (4, 4), (6, 69), (7, 71), (8, 55), (9, 76), (10, 59), (11, 57), (13, 13), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126705) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 81) (jcc_rel32_effect_step 0x126705 5 0x8a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1266b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1266b9 :=
  Rest.liftedBlock (rest_l1266b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1266b9 x hx)

theorem rest_l12670b_1 [Bindings] (code : CodeMap) :
    Rest (n := 81) code lifted (codeRange 0x12670b bytes_l12670b) [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]
      5 0x126763 bytes_l12670b_1 b_l12670b_1 := by
  have f20 : InstrSpec 0x126763 [0x89, 0x4B, 0x28] (StorePre 0x126763 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126763 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126763 1 (.base 3 (.d8 0x28)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126763 1 (.base 3 (.d8 0x28))).toInstrSpec (mov_m32_r32_low_effect_step 0x126763 1 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x126766 [0x89, 0x53, 0x2C] (StorePre 0x126766 3 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x126766 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126766 2 (.base 3 (.d8 0x2c)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126766 2 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m32_r32_low_effect_step 0x126766 2 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x126769 [0xC6, 0x43, 0x30, 0x00] (StorePre 0x126769 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126769 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x126769 (.base 3 (.d8 0x30)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x126769 (.base 3 (.d8 0x30)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x126769 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x12676d [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x12676d 6 (fun s => AddrMode.addr (.base 3 .none) s (0x12676d + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12676d 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x12676d 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x12676d (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126766) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126769) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12676d) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126773) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 85) (jmp_rel32_effect_step 0x126773 0xfffffdea (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l12670b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12670b bytes_l12670b) (entryMap (live .l12670b))
      25 0x12670b bytes_l12670b b_l12670b := by
  have f0 : InstrSpec 0x12670b [0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x12670b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12670b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12670b 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12670b 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r32_m32_low_effect_step 0x12670b 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12670f [0x48, 0x8B, 0x74, 0x24, 0x58] (LoadPre 0x12670f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12670f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12670f 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12670f 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x12670f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x126714 [0x89, 0x44, 0x24, 0x08] (StorePre 0x126714 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126714 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126714 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126714 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x126714 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x126718 [0x4C, 0x89, 0x44, 0x24, 0x0C] (StorePre 0x126718 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126718 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126718 8 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126718 8 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x126718 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12671d [0x4C, 0x89, 0x5C, 0x24, 0x14] (StorePre 0x12671d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x12671d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12671d 11 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12671d 11 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x12671d 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x126722 [0x8B, 0x44, 0x24, 0x18] (LoadPre 0x126722 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126722 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126722 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x126722 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x126722 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x126726 [0x89, 0x44, 0x24, 0x78] (StorePre 0x126726 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126726 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126726 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126726 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m32_r32_low_effect_step 0x126726 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x12672a [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x12672a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12672a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12672a 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12672a 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12672a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x12672f [0x48, 0x89, 0x44, 0x24, 0x70] (StorePre 0x12672f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12672f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12672f 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12672f 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x12672f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x126734 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x126734 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126734 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126734 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126734 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x126734 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x126739 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x126739 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126739 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126739 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x126739 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x126739 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x12673e [0x8B, 0x44, 0x24, 0x78] (LoadPre 0x12673e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x12673e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12673e 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x12673e 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r32_m32_low_effect_step 0x12673e 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x126742 [0x89, 0x43, 0x18] (StorePre 0x126742 3 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126742 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126742 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x126742 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x126742 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x126745 [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x126745 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126745 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126745 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x126745 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x126745 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x12674a [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x12674a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12674a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12674a 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12674a 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x12674a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x12674f [0x48, 0x89, 0x7B, 0x10] (StorePre 0x12674f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12674f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12674f 7 (.base 3 (.d8 0x10)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12674f 7 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12674f 0x48 (by decide) 7 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x126753 [0x48, 0x89, 0x43, 0x08] (StorePre 0x126753 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126753 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126753 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x126753 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x126753 0x48 (by decide) 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x126757 [0x44, 0x89, 0x6B, 0x04] (StorePre 0x126757 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x126757 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126757 13 (.base 3 (.d8 0x4)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x126757 13 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x126757 0x44 (by decide) 5 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x12675b [0x44, 0x89, 0x53, 0x1C] (StorePre 0x12675b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x12675b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12675b 10 (.base 3 (.d8 0x1c)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x12675b 10 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m32_r32_effect_step 0x12675b 0x44 (by decide) 2 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x12675f [0x48, 0x89, 0x73, 0x20] (StorePre 0x12675f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x12675f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12675f 6 (.base 3 (.d8 0x20)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12675f 6 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x12675f 0x48 (by decide) 6 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12670f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126714) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126718) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12671d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126722) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126726) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12672a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12672f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126734) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126739) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12673e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126742) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126745) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12674a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12674f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126753) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126757) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12675b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12675f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 72), (1, 53), (2, 2), (3, 3), (4, 4), (6, 55), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126763) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l12670b_1 code

theorem block_l12670b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12670b :=
  Rest.liftedBlock (rest_l12670b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12670b x hx)

theorem rest_l126778 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126778 bytes_l126778) (entryMap (live .l126778))
      7 0x126778 bytes_l126778 b_l126778 := by
  have f0 : InstrSpec 0x126778 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x126778 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126778 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126778 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x126778 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x126778 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12677d [0x49, 0x89, 0xC0] (fun s => s.RIP = 0x12677d) (movR64R64Effect 0x12677d 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x12677d 8 0).toInstrSpec (mov_r64_r64_effect_step 0x12677d 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x126780 [0x49, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x126780) (shlR64Effect 0x126780 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x126780 4 8 32).toInstrSpec (shl_r64_imm8_effect_step 0x126780 0x49 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x126784 [0x49, 0x83, 0xC8, 0x13] (fun s => s.RIP = 0x126784) (orR64Imm8Effect 0x126784 8 0x13)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x126784 8 0x13).toInstrSpec (or_r64_imm8_effect_step 0x126784 0x49 0xc8 0x13 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x126788 [0xB9, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x126788) (movR32Imm32Effect 0x126788 5 1 0x1)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x126788 5 1 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x126788 0xb9 (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x12678d [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x12678d) (xorR32R32Effect 0x12678d 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12678d 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x12678d 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12677d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 54), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126780) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 56), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126784) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 58), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126788) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 58), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12678d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 58), (9, 9), (10, 10), (11, 11), (14, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126790) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 64) (jmp_rel32_effect_step 0x126790 0xfffffe69 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126778 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126778 :=
  Rest.liftedBlock (rest_l126778 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126778 x hx)

theorem rest_l126795 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x126795 bytes_l126795) (entryMap (live .l126795))
      4 0x126795 bytes_l126795 b_l126795 := by
  have f0 : InstrSpec 0x126795 [0x49, 0xBE, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x126795) (movR64Imm64Effect 0x126795 14 0xffffffff00000000)
      [] [] [.reg 14, .rip] :=
    (movR64Imm64Effect_footprint 0x126795 14 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x126795 0x49 0xbe (by decide) (by decide) 0xffffffff00000000) pre_rip
  have f1 : InstrSpec 0x12679f [0x4D, 0x21, 0xDE] (fun s => s.RIP = 0x12679f) (andR64R64Effect 0x12679f 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x12679f 14 11).toInstrSpec (and_r64_r64_effect_step 0x12679f 0x4d 0xde (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1267a2 [0x44, 0x8B, 0x4C, 0x24, 0x54] (LoadPre 0x1267a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x1267a2 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1267a2 9 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x1267a2 9 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_effect_step 0x1267a2 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12679f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267a2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 10), (11, 11), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267a7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x1267a7 0xfffffe52 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l126795 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l126795 :=
  Rest.liftedBlock (rest_l126795 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l126795 x hx)

theorem rest_l1267ac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1267ac bytes_l1267ac) (entryMap (live .l1267ac))
      4 0x1267ac bytes_l1267ac b_l1267ac := by
  have f0 : InstrSpec 0x1267ac [0x31, 0xC9] (fun s => s.RIP = 0x1267ac) (xorR32R32Effect 0x1267ac 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1267ac 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1267ac 0xc9 (by decide)) pre_rip
  have f1 : InstrSpec 0x1267ae [0x41, 0xB8, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1267ae) (movR32Imm32Effect 0x1267ae 6 8 0xc)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x1267ae 6 8 0xc).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1267ae 0x41 0xb8 (by decide) (by decide) 0xc) pre_rip
  have f2 : InstrSpec 0x1267b4 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x1267b4) (xorR32R32Effect 0x1267b4 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1267b4 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1267b4 0x45 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267ae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267b4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267b7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x1267b7 0xfffffe42 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1267ac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1267ac :=
  Rest.liftedBlock (rest_l1267ac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1267ac x hx)

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

theorem_by block_l1262e0_eval :
    program.runBlock (dialect code) ⟨.l1262e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126308_eval :
    program.runBlock (dialect code) ⟨.l126308, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12631a_eval :
    program.runBlock (dialect code) ⟨.l12631a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126322_eval :
    program.runBlock (dialect code) ⟨.l126322, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12632f_eval :
    program.runBlock (dialect code) ⟨.l12632f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126356_eval :
    program.runBlock (dialect code) ⟨.l126356, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126365_eval :
    program.runBlock (dialect code) ⟨.l126365, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12636f_eval :
    program.runBlock (dialect code) ⟨.l12636f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126377_eval :
    program.runBlock (dialect code) ⟨.l126377, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126384_eval :
    program.runBlock (dialect code) ⟨.l126384, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1263a2_eval :
    program.runBlock (dialect code) ⟨.l1263a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1263af_eval :
    program.runBlock (dialect code) ⟨.l1263af, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1263ce_eval :
    program.runBlock (dialect code) ⟨.l1263ce, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1263d9_eval :
    program.runBlock (dialect code) ⟨.l1263d9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126420_eval :
    program.runBlock (dialect code) ⟨.l126420, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12642f_eval :
    program.runBlock (dialect code) ⟨.l12642f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126480_eval :
    program.runBlock (dialect code) ⟨.l126480, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126488_eval :
    program.runBlock (dialect code) ⟨.l126488, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1264c1_eval :
    program.runBlock (dialect code) ⟨.l1264c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1264f3_eval :
    program.runBlock (dialect code) ⟨.l1264f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1264f8_eval :
    program.runBlock (dialect code) ⟨.l1264f8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126562_eval :
    program.runBlock (dialect code) ⟨.l126562, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126577_eval :
    program.runBlock (dialect code) ⟨.l126577, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1265d4_eval :
    program.runBlock (dialect code) ⟨.l1265d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1265e4_eval :
    program.runBlock (dialect code) ⟨.l1265e4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1265f0_eval :
    program.runBlock (dialect code) ⟨.l1265f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1265fe_eval :
    program.runBlock (dialect code) ⟨.l1265fe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126663_eval :
    program.runBlock (dialect code) ⟨.l126663, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126674_eval :
    program.runBlock (dialect code) ⟨.l126674, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1266b9_eval :
    program.runBlock (dialect code) ⟨.l1266b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12670b_eval :
    program.runBlock (dialect code) ⟨.l12670b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126778_eval :
    program.runBlock (dialect code) ⟨.l126778, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l126795_eval :
    program.runBlock (dialect code) ⟨.l126795, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1267ac_eval :
    program.runBlock (dialect code) ⟨.l1267ac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
