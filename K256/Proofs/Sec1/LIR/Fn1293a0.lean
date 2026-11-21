import K256.Proofs.Sec1.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Sec1.LIR.Generated.Values

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

theorem rest_l1293a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1293a0 bytes_l1293a0) (entryMap (live .l1293a0))
      13 0x1293a0 bytes_l1293a0 b_l1293a0 := by
  have f0 : InstrSpec 0x1293a0 [0x55] (PushPre 0x1293a0 1) (pushR64Effect 0x1293a0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1293a0 1 5).toInstrSpec (push_r64_effect_step 0x1293a0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x1293a1 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x1293a1) (movR64R64Effect 0x1293a1 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x1293a1 5 4).toInstrSpec (mov_r64_r64_effect_step 0x1293a1 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1293a4 [0x41, 0x57] (PushPre 0x1293a4 2) (pushR64Effect 0x1293a4 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1293a4 2 15).toInstrSpec (push_r64_rex_effect_step 0x1293a4 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1293a6 [0x41, 0x56] (PushPre 0x1293a6 2) (pushR64Effect 0x1293a6 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1293a6 2 14).toInstrSpec (push_r64_rex_effect_step 0x1293a6 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1293a8 [0x41, 0x55] (PushPre 0x1293a8 2) (pushR64Effect 0x1293a8 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1293a8 2 13).toInstrSpec (push_r64_rex_effect_step 0x1293a8 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1293aa [0x41, 0x54] (PushPre 0x1293aa 2) (pushR64Effect 0x1293aa 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1293aa 2 12).toInstrSpec (push_r64_rex_effect_step 0x1293aa 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1293ac [0x53] (PushPre 0x1293ac 1) (pushR64Effect 0x1293ac 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x1293ac 1 3).toInstrSpec (push_r64_effect_step 0x1293ac 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1293ad [0x48, 0x83, 0xEC, 0x38] (fun s => s.RIP = 0x1293ad) (subR64Imm8Effect 0x1293ad 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x1293ad 4 0x38).toInstrSpec (sub_r64_imm8_effect_step 0x1293ad 0x48 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1293b1 [0x48, 0x89, 0xCB] (fun s => s.RIP = 0x1293b1) (movR64R64Effect 0x1293b1 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1293b1 3 1).toInstrSpec (mov_r64_r64_effect_step 0x1293b1 0x48 0xcb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1293b4 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x1293b4) (movR64R64Effect 0x1293b4 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1293b4 13 2).toInstrSpec (mov_r64_r64_effect_step 0x1293b4 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1293b7 [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x1293b7) (movR64R64Effect 0x1293b7 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1293b7 14 7).toInstrSpec (mov_r64_r64_effect_step 0x1293b7 0x49 0xfe (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1293ba [0xF6, 0xC3, 0x01] (fun s => s.RIP = 0x1293ba) (testR8Imm8LowEffect 0x1293ba 3 0x1)
      [.gpr 3] [] [.flags, .rip] :=
    (testR8Imm8LowEffect_footprint 0x1293ba 3 0x1).toInstrSpec (test_r8_imm8_low_effect_step 0x1293ba 0xc3 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293a6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293a8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293aa) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293ac) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293ad) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293b1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293b4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293b7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293ba) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 73), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293bd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel32_effect_step 0x1293bd 5 0x168) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1293a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1293a0 :=
  Rest.liftedBlock (rest_l1293a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1293a0 x hx)

theorem rest_l1293c3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1293c3 bytes_l1293c3) (entryMap (live .l1293c3))
      3 0x1293c3 bytes_l1293c3 b_l1293c3 := by
  have f0 : InstrSpec 0x1293c3 [0x41, 0x0F, 0xB6, 0x45, 0x00] (LoadPre 0x1293c3 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1293c3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1293c3 5 0 (.base 13 (.d8 0x0)))
      [.gpr 13] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1293c3 5 0 (.base 13 (.d8 0x0))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1293c3 0x41 (by decide) 0 (.base 13 (.d8 0x0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1293c8 [0x84, 0xC0] (fun s => s.RIP = 0x1293c8) (testR8R8Effect 0x1293c8 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1293c8 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1293c8 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293c8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1293ca 4 0x17b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1293c3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1293c3 :=
  Rest.liftedBlock (rest_l1293c3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1293c3 x hx)

theorem rest_l1293d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1293d0 bytes_l1293d0) (entryMap (live .l1293d0))
      5 0x1293d0 bytes_l1293d0 b_l1293d0 := by
  have f0 : InstrSpec 0x1293d0 [0x48, 0x89, 0x75, 0xB0] (StorePre 0x1293d0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x1293d0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1293d0 6 (.base 5 (.d8 0xb0)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1293d0 6 (.base 5 (.d8 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x1293d0 0x48 (by decide) 6 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1293d4 [0x48, 0x8B, 0x4E, 0x18] (LoadPre 0x1293d4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1293d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1293d4 1 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1293d4 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1293d4 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1293d8 [0x48, 0x89, 0x4D, 0xA8] (StorePre 0x1293d8 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x1293d8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1293d8 1 (.base 5 (.d8 0xa8)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1293d8 1 (.base 5 (.d8 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x1293d8 0x48 (by decide) 1 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1293dc [0x48, 0xC7, 0x45, 0xD0, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1293dc 8 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x1293dc + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1293dc (.base 5 (.d8 0xd0)) 0x0)
      [.gpr 5] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1293dc (.base 5 (.d8 0xd0)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1293dc 0x48 (by decide) (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (13, 13), (14, 14)]) (p' := 0x1293d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (5, 5), (6, 6), (13, 13), (14, 14)]) (p' := 0x1293d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (5, 5), (6, 6), (13, 13), (14, 14)]) (p' := 0x1293dc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (5, 5), (6, 6), (13, 13), (14, 14)]) (p' := 0x1293e4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 58) (jmp_rel8_effect_step 0x1293e4 0x1a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1293d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1293d0 :=
  Rest.liftedBlock (rest_l1293d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1293d0 x hx)

theorem rest_l1293f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1293f0 bytes_l1293f0) (entryMap (live .l1293f0))
      4 0x1293f0 bytes_l1293f0 b_l1293f0 := by
  have f0 : InstrSpec 0x1293f0 [0x41, 0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x1293f0 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1293f0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1293f0 5 0 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1293f0 5 0 (.sib 12 none 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1293f0 0x41 (by decide) 0 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1293f5 [0x4D, 0x89, 0xE5] (fun s => s.RIP = 0x1293f5) (movR64R64Effect 0x1293f5 13 12)
      [.gpr 12] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1293f5 13 12).toInstrSpec (mov_r64_r64_effect_step 0x1293f5 0x4d 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1293f8 [0x84, 0xC0] (fun s => s.RIP = 0x1293f8) (testR8R8Effect 0x1293f8 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1293f8 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1293f8 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293f8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293fa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x1293fa 4 0x14b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1293f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1293f0 :=
  Rest.liftedBlock (rest_l1293f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1293f0 x hx)

theorem rest_l129400 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129400 bytes_l129400) (entryMap (live .l129400))
      4 0x129400 bytes_l129400 b_l129400 := by
  have f0 : InstrSpec 0x129400 [0x4D, 0x8D, 0x65, 0x01] (fun s => s.RIP = 0x129400) (leaR64Effect 0x129400 12 (.base 13 (.d8 0x1)))
      [.gpr 13] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x129400 12 (.base 13 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x129400 0x4d (by decide) 4 (.base 13 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129404 [0x44, 0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x129404) (movzxR32R8Effect 0x129404 4 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movzxR32R8Effect_footprint 0x129404 4 15 0).toInstrSpec (movzx_r32_r8_rex_effect_step 0x129404 0x44 (by decide) 0xf8 (by decide)) pre_rip
  have f2 : InstrSpec 0x129408 [0x84, 0xC0] (fun s => s.RIP = 0x129408) (testR8R8Effect 0x129408 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129408 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x129408 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 53), (13, 13), (14, 14)]) (p' := 0x129404) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 53), (13, 13), (14, 14), (15, 55)]) (p' := 0x129408) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 53), (13, 13), (14, 14), (15, 55), (20, 57)]) (p' := 0x12940a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x12940a 8 0x24) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129400 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129400 :=
  Rest.liftedBlock (rest_l129400 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129400 x hx)

theorem rest_l12940c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12940c bytes_l12940c) (entryMap (live .l12940c))
      3 0x12940c bytes_l12940c b_l12940c := by
  have f0 : InstrSpec 0x12940c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x12940c) (movR64R64Effect 0x12940c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12940c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x12940c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12940f [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x12940f) (movR64R64Effect 0x12940f 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12940f 6 12).toInstrSpec (mov_r64_r64_effect_step 0x12940f 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129412 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x129412) (movR64R64Effect 0x129412 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129412 2 15).toInstrSpec (mov_r64_r64_effect_step 0x129412 0x4c 0xfa (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(12, 12), (14, 14), (15, 15)]) (p' := 0x12940f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(12, 12), (14, 14), (15, 15)]) (p' := 0x129412) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(12, 12), (14, 14), (15, 15)]) (p' := 0x129415) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12940c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12940c :=
  Rest.liftedBlock (rest_l12940c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12940c x hx)

theorem rest_l129418 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129418 bytes_l129418) (entryMap (live .l129418))
      2 0x129418 bytes_l129418 b_l129418 := by
  have f0 : InstrSpec 0x129418 [0x84, 0xC0] (fun s => s.RIP = 0x129418) (testR8R8Effect 0x129418 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129418 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x129418 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12941a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x12941a 5 0x12f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129418 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129418 :=
  Rest.liftedBlock (rest_l129418 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129418 x hx)

theorem rest_l129420 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129420 bytes_l129420) (entryMap (live .l129420))
      2 0x129420 bytes_l129420 b_l129420 := by
  have f0 : InstrSpec 0x129420 [0x4D, 0x01, 0xFC] (fun s => s.RIP = 0x129420) (addR64R64Effect 0x129420 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x129420 12 15).toInstrSpec (add_r64_r64_effect_step 0x129420 0x4d 0xfc (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129423) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x129423 0xcb (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129420 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129420 :=
  Rest.liftedBlock (rest_l129420 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129420 x hx)

theorem rest_l129430 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129430 bytes_l129430) (entryMap (live .l129430))
      2 0x129430 bytes_l129430 b_l129430 := by
  have f0 : InstrSpec 0x129430 [0x3C, 0x80] (fun s => s.RIP = 0x129430) (cmpAlImm8Effect 0x129430 0x80)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpAlImm8Effect_footprint 0x129430 0x80).toInstrSpec (cmp_al_imm8_effect_step 0x129430 0x80) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)]) (p' := 0x129432) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x129432 4 0x21) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129430 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129430 :=
  Rest.liftedBlock (rest_l129430 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129430 x hx)

theorem rest_l129434 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129434 bytes_l129434) (entryMap (live .l129434))
      2 0x129434 bytes_l129434 b_l129434 := by
  have f0 : InstrSpec 0x129434 [0x41, 0x81, 0xFF, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129434) (cmpR32Imm32Effect 0x129434 7 15 0xc0)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR32Imm32Effect_footprint 0x129434 7 15 0xc0).toInstrSpec (cmp_r32_imm32_rex_effect_step 0x129434 0x41 0xff 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)]) (p' := 0x12943b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12943b 5 0x3f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129434 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129434 :=
  Rest.liftedBlock (rest_l129434 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129434 x hx)

theorem rest_l12943d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12943d bytes_l12943d) (entryMap (live .l12943d))
      5 0x12943d bytes_l12943d b_l12943d := by
  have f0 : InstrSpec 0x12943d [0x4C, 0x8B, 0x7D, 0xD0] (LoadPre 0x12943d (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x12943d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12943d 15 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x12943d 15 (.base 5 (.d8 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x12943d 0x4c (by decide) 7 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129441 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x129441) (movR64R64Effect 0x129441 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x129441 0 15).toInstrSpec (mov_r64_r64_effect_step 0x129441 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129444 [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x129444) (shlR64Effect 0x129444 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x129444 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x129444 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129448 [0x48, 0xC7, 0x45, 0xC8, 0x20, 0x00, 0x00, 0x60] (StorePre 0x129448 8 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x129448 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x129448 (.base 5 (.d8 0xc8)) 0x60000020)
      [.gpr 5] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x129448 (.base 5 (.d8 0xc8)) 0x60000020).toInstrSpec (mov_m64_imm32_effect_step 0x129448 0x48 (by decide) (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide) 0x60000020) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (5, 5), (14, 14), (15, 53)]) (p' := 0x129441) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (5, 5), (14, 14), (15, 53)]) (p' := 0x129444) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (5, 5), (14, 14), (15, 53)]) (p' := 0x129448) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 57), (3, 3), (5, 5), (14, 14), (15, 53)]) (p' := 0x129450) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 60) (jmp_rel32_effect_step 0x129450 0x9d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12943d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12943d :=
  Rest.liftedBlock (rest_l12943d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12943d x hx)

theorem rest_l129455 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129455 bytes_l129455) (entryMap (live .l129455))
      4 0x129455 bytes_l129455 b_l129455 := by
  have f0 : InstrSpec 0x129455 [0x45, 0x0F, 0xB7, 0x7D, 0x01] (LoadPre 0x129455 (fun s => AddrMode.addr (.base 13 (.d8 0x1)) s (0x129455 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x129455 5 15 (.base 13 (.d8 0x1)))
      [.gpr 13] [] [.reg 15, .rip] :=
    (movzxR32M16Effect_footprint 0x129455 5 15 (.base 13 (.d8 0x1))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x129455 0x45 (by decide) 7 (.base 13 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12945a [0x49, 0x8D, 0x75, 0x03] (fun s => s.RIP = 0x12945a) (leaR64Effect 0x12945a 6 (.base 13 (.d8 0x3)))
      [.gpr 13] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x12945a 6 (.base 13 (.d8 0x3))).toInstrSpec (lea_r64_effect_step 0x12945a 0x49 (by decide) 6 (.base 13 (.d8 0x3)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12945e [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x12945e) (movR64R64Effect 0x12945e 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12945e 7 14).toInstrSpec (mov_r64_r64_effect_step 0x12945e 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129461 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x129461) (movR64R64Effect 0x129461 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129461 2 15).toInstrSpec (mov_r64_r64_effect_step 0x129461 0x4c 0xfa (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(13, 13), (14, 14), (15, 53)]) (p' := 0x12945a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(13, 13), (14, 14), (15, 53)]) (p' := 0x12945e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(13, 13), (14, 14), (15, 53)]) (p' := 0x129461) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(13, 13), (14, 14), (15, 53)]) (p' := 0x129464) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l129455 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129455 :=
  Rest.liftedBlock (rest_l129455 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129455 x hx)

theorem rest_l129467 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129467 bytes_l129467) (entryMap (live .l129467))
      2 0x129467 bytes_l129467 b_l129467 := by
  have f0 : InstrSpec 0x129467 [0x84, 0xC0] (fun s => s.RIP = 0x129467) (testR8R8Effect 0x129467 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129467 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x129467 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129469) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x129469 5 0xe0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129467 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129467 :=
  Rest.liftedBlock (rest_l129467 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129467 x hx)

theorem rest_l12946f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12946f bytes_l12946f) (entryMap (live .l12946f))
      3 0x12946f bytes_l12946f b_l12946f := by
  have f0 : InstrSpec 0x12946f [0x4F, 0x8D, 0x24, 0x2F] (fun s => s.RIP = 0x12946f) (leaR64Effect 0x12946f 12 (.sib 15 (some 13) 0 .none))
      [.gpr 15, .gpr 13] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x12946f 12 (.sib 15 (some 13) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12946f 0x4f (by decide) 4 (.sib 15 (some 13) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129473 [0x49, 0x83, 0xC4, 0x03] (fun s => s.RIP = 0x129473) (addR64Imm8Effect 0x129473 12 0x3)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129473 12 0x3).toInstrSpec (add_r64_imm8_effect_step 0x129473 0x49 0xc4 0x3 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129473) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129477) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x129477 0xffffff74 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12946f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12946f :=
  Rest.liftedBlock (rest_l12946f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12946f x hx)

theorem rest_l12947c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12947c bytes_l12947c) (entryMap (live .l12947c))
      3 0x12947c bytes_l12947c b_l12947c := by
  have f0 : InstrSpec 0x12947c [0xB9, 0x20, 0x00, 0x00, 0x60] (fun s => s.RIP = 0x12947c) (movR32Imm32Effect 0x12947c 5 1 0x60000020)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x12947c 5 1 0x60000020).toInstrSpec (mov_r32_imm32_effect_step 0x12947c 0xb9 (by decide) 0x60000020) pre_rip
  have f1 : InstrSpec 0x129481 [0xA8, 0x01] (fun s => s.RIP = 0x129481) (testAlImm8Effect 0x129481 0x1)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x129481 0x1).toInstrSpec (test_al_imm8_effect_step 0x129481 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14)]) (p' := 0x129481) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (19, 55)]) (p' := 0x129483) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x129483 4 0xb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12947c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12947c :=
  Rest.liftedBlock (rest_l12947c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12947c x hx)

theorem rest_l129485 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129485 bytes_l129485) (entryMap (live .l129485))
      3 0x129485 bytes_l129485 b_l129485 := by
  have f0 : InstrSpec 0x129485 [0x41, 0x8B, 0x4D, 0x01] (LoadPre 0x129485 (fun s => AddrMode.addr (.base 13 (.d8 0x1)) s (0x129485 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x129485 1 (.base 13 (.d8 0x1)))
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x129485 1 (.base 13 (.d8 0x1))).toInstrSpec (mov_r32_m32_effect_step 0x129485 0x41 (by decide) 1 (.base 13 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129489 [0x49, 0x83, 0xC5, 0x05] (fun s => s.RIP = 0x129489) (addR64Imm8Effect 0x129489 13 0x5)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129489 13 0x5).toInstrSpec (add_r64_imm8_effect_step 0x129489 0x49 0xc5 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12948d [0x4D, 0x89, 0xEC] (fun s => s.RIP = 0x12948d) (movR64R64Effect 0x12948d 12 13)
      [.gpr 13] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x12948d 12 13).toInstrSpec (mov_r64_r64_effect_step 0x12948d 0x4d 0xec (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (5, 5), (6, 6), (13, 13), (14, 14)]) (p' := 0x129489) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (5, 5), (6, 6), (13, 55), (14, 14)]) (p' := 0x12948d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (5, 5), (6, 6), (12, 57), (13, 55), (14, 14)]) (p' := 0x129490) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l129485 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129485 :=
  Rest.liftedBlock (rest_l129485 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129485 x hx)

theorem rest_l129490 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129490 bytes_l129490) (entryMap (live .l129490))
      2 0x129490 bytes_l129490 b_l129490 := by
  have f0 : InstrSpec 0x129490 [0xA8, 0x02] (fun s => s.RIP = 0x129490) (testAlImm8Effect 0x129490 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x129490 0x2).toInstrSpec (test_al_imm8_effect_step 0x129490 0x2) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14), (19, 53)]) (p' := 0x129492) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x129492 5 0x19) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129490 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129490 :=
  Rest.liftedBlock (rest_l129490 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129490 x hx)

theorem rest_l129494 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129494 bytes_l129494) (entryMap (live .l129494))
      4 0x129494 bytes_l129494 b_l129494 := by
  have f0 : InstrSpec 0x129494 [0x31, 0xD2] (fun s => s.RIP = 0x129494) (xorR32R32Effect 0x129494 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129494 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x129494 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x129496 [0x4C, 0x8B, 0x7D, 0xD0] (LoadPre 0x129496 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129496 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129496 15 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x129496 15 (.base 5 (.d8 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x129496 0x4c (by decide) 7 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12949a [0xA8, 0x04] (fun s => s.RIP = 0x12949a) (testAlImm8Effect 0x12949a 0x4)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x12949a 0x4).toInstrSpec (test_al_imm8_effect_step 0x12949a 0x4) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14)]) (p' := 0x129496) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14), (15, 55)]) (p' := 0x12949a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14), (15, 55), (19, 57)]) (p' := 0x12949c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x12949c 4 0x20) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129494 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129494 :=
  Rest.liftedBlock (rest_l129494 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129494 x hx)

theorem rest_l12949e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12949e bytes_l12949e) (entryMap (live .l12949e))
      4 0x12949e bytes_l12949e b_l12949e := by
  have f0 : InstrSpec 0x12949e [0x41, 0x0F, 0xB7, 0x34, 0x24] (LoadPre 0x12949e (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x12949e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x12949e 5 6 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x12949e 5 6 (.sib 12 none 0 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x12949e 0x41 (by decide) 6 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1294a3 [0x49, 0x83, 0xC4, 0x02] (fun s => s.RIP = 0x1294a3) (addR64Imm8Effect 0x1294a3 12 0x2)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1294a3 12 0x2).toInstrSpec (add_r64_imm8_effect_step 0x1294a3 0x49 0xc4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1294a7 [0xA8, 0x08] (fun s => s.RIP = 0x1294a7) (testAlImm8Effect 0x1294a7 0x8)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x1294a7 0x8).toInstrSpec (test_al_imm8_effect_step 0x1294a7 0x8) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 53), (12, 12), (14, 14), (15, 15)]) (p' := 0x1294a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 53), (12, 55), (14, 14), (15, 15)]) (p' := 0x1294a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 53), (12, 55), (14, 14), (15, 15), (19, 57)]) (p' := 0x1294a9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1294a9 5 0x19) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12949e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12949e :=
  Rest.liftedBlock (rest_l12949e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12949e x hx)

theorem rest_l1294ab [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1294ab bytes_l1294ab) (entryMap (live .l1294ab))
      1 0x1294ab bytes_l1294ab b_l1294ab := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x1294ab 0x20 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1294ab [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1294ab :=
  Rest.liftedBlock (rest_l1294ab code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1294ab x hx)

theorem rest_l1294ad [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1294ad bytes_l1294ad) (entryMap (live .l1294ad))
      5 0x1294ad bytes_l1294ad b_l1294ad := by
  have f0 : InstrSpec 0x1294ad [0x41, 0x0F, 0xB7, 0x14, 0x24] (LoadPre 0x1294ad (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1294ad + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1294ad 5 2 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x1294ad 5 2 (.sib 12 none 0 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1294ad 0x41 (by decide) 2 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1294b2 [0x49, 0x83, 0xC4, 0x02] (fun s => s.RIP = 0x1294b2) (addR64Imm8Effect 0x1294b2 12 0x2)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1294b2 12 0x2).toInstrSpec (add_r64_imm8_effect_step 0x1294b2 0x49 0xc4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1294b6 [0x4C, 0x8B, 0x7D, 0xD0] (LoadPre 0x1294b6 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x1294b6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1294b6 15 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1294b6 15 (.base 5 (.d8 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x1294b6 0x4c (by decide) 7 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1294ba [0xA8, 0x04] (fun s => s.RIP = 0x1294ba) (testAlImm8Effect 0x1294ba 0x4)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x1294ba 0x4).toInstrSpec (test_al_imm8_effect_step 0x1294ba 0x4) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14)]) (p' := 0x1294b2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 55), (14, 14)]) (p' := 0x1294b6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 55), (14, 14), (15, 57)]) (p' := 0x1294ba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 55), (14, 14), (15, 57), (19, 59)]) (p' := 0x1294bc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x1294bc 5 0xe0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1294ad [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1294ad :=
  Rest.liftedBlock (rest_l1294ad code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1294ad x hx)

theorem rest_l1294be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1294be bytes_l1294be) (entryMap (live .l1294be))
      3 0x1294be bytes_l1294be b_l1294be := by
  have f0 : InstrSpec 0x1294be [0x31, 0xF6] (fun s => s.RIP = 0x1294be) (xorR32R32Effect 0x1294be 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1294be 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1294be 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x1294c0 [0xA8, 0x08] (fun s => s.RIP = 0x1294c0) (testAlImm8Effect 0x1294c0 0x8)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x1294c0 0x8).toInstrSpec (test_al_imm8_effect_step 0x1294c0 0x8) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 53), (12, 12), (14, 14), (15, 15)]) (p' := 0x1294c0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 53), (12, 12), (14, 14), (15, 15), (19, 55)]) (p' := 0x1294c2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1294c2 4 0x9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1294be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1294be :=
  Rest.liftedBlock (rest_l1294be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1294be x hx)

theorem rest_l1294c4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1294c4 bytes_l1294c4) (entryMap (live .l1294c4))
      2 0x1294c4 bytes_l1294c4 b_l1294c4 := by
  have f0 : InstrSpec 0x1294c4 [0x45, 0x0F, 0xB7, 0x3C, 0x24] (LoadPre 0x1294c4 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1294c4 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1294c4 5 15 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 15, .rip] :=
    (movzxR32M16Effect_footprint 0x1294c4 5 15 (.sib 12 none 0 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1294c4 0x45 (by decide) 7 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1294c9 [0x49, 0x83, 0xC4, 0x02] (fun s => s.RIP = 0x1294c9) (addR64Imm8Effect 0x1294c9 12 0x2)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1294c9 12 0x2).toInstrSpec (add_r64_imm8_effect_step 0x1294c9 0x49 0xc4 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14), (15, 53)]) (p' := 0x1294c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 53)]) (p' := 0x1294cd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l1294c4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1294c4 :=
  Rest.liftedBlock (rest_l1294c4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1294c4 x hx)

theorem rest_l1294cd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1294cd bytes_l1294cd) (entryMap (live .l1294cd))
      2 0x1294cd bytes_l1294cd b_l1294cd := by
  have f0 : InstrSpec 0x1294cd [0xA8, 0x10] (fun s => s.RIP = 0x1294cd) (testAlImm8Effect 0x1294cd 0x10)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x1294cd 0x10).toInstrSpec (test_al_imm8_effect_step 0x1294cd 0x10) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15), (19, 53)]) (p' := 0x1294cf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1294cf 5 0x49) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1294cd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1294cd :=
  Rest.liftedBlock (rest_l1294cd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1294cd x hx)

theorem rest_l1294d1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1294d1 bytes_l1294d1) (entryMap (live .l1294d1))
      2 0x1294d1 bytes_l1294d1 b_l1294d1 := by
  have f0 : InstrSpec 0x1294d1 [0xA8, 0x20] (fun s => s.RIP = 0x1294d1) (testAlImm8Effect 0x1294d1 0x20)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x1294d1 0x20).toInstrSpec (test_al_imm8_effect_step 0x1294d1 0x20) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15), (19, 53)]) (p' := 0x1294d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1294d3 4 0xb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1294d1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1294d1 :=
  Rest.liftedBlock (rest_l1294d1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1294d1 x hx)

theorem rest_l1294d5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1294d5 bytes_l1294d5) (entryMap (live .l1294d5))
      3 0x1294d5 bytes_l1294d5 b_l1294d5 := by
  have f0 : InstrSpec 0x1294d5 [0x0F, 0xB7, 0xC6] (fun s => s.RIP = 0x1294d5) (movzxR32R16Effect 0x1294d5 3 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movzxR32R16Effect_footprint 0x1294d5 3 0 6).toInstrSpec (movzx_r32_r16_effect_step 0x1294d5 0xc6 (by decide)) pre_rip
  have f1 : InstrSpec 0x1294d8 [0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x1294d8) (shlR32Effect 0x1294d8 3 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x1294d8 3 0 4).toInstrSpec (shl_r32_imm8_effect_step 0x1294d8 0xe0 0x4 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1294db [0x0F, 0xB7, 0x74, 0x03, 0x08] (LoadPre 0x1294db (fun s => AddrMode.addr (.sib 3 (some 0) 0 (.d8 0x8)) s (0x1294db + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1294db 5 6 (.sib 3 (some 0) 0 (.d8 0x8)))
      [.gpr 3, .gpr 0] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x1294db 5 6 (.sib 3 (some 0) 0 (.d8 0x8))).toInstrSpec (movzx_r32_m16_effect_step 0x1294db 6 (.sib 3 (some 0) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x1294d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x1294db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (5, 5), (6, 57), (14, 14), (15, 15)]) (p' := 0x1294e0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l1294d5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1294d5 :=
  Rest.liftedBlock (rest_l1294d5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1294d5 x hx)

theorem rest_l1294e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1294e0 bytes_l1294e0) (entryMap (live .l1294e0))
      5 0x1294e0 bytes_l1294e0 b_l1294e0 := by
  have f0 : InstrSpec 0x1294e0 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x1294e0) (movR64R64Effect 0x1294e0 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1294e0 0 15).toInstrSpec (mov_r64_r64_effect_step 0x1294e0 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1294e3 [0x48, 0xC1, 0xE0, 0x04] (fun s => s.RIP = 0x1294e3) (shlR64Effect 0x1294e3 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x1294e3 4 0 4).toInstrSpec (shl_r64_imm8_effect_step 0x1294e3 0x48 0xe0 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1294e7 [0x89, 0x4D, 0xC8] (StorePre 0x1294e7 3 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1294e7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1294e7 1 (.base 5 (.d8 0xc8)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1294e7 1 (.base 5 (.d8 0xc8))).toInstrSpec (mov_m32_r32_low_effect_step 0x1294e7 1 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1294ea [0x66, 0x89, 0x55, 0xCC] (StorePre 0x1294ea 4 (fun s => AddrMode.addr (.base 5 (.d8 0xcc)) s (0x1294ea + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1294ea 4 2 (.base 5 (.d8 0xcc)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM16R16Effect_footprint 0x1294ea 4 2 (.base 5 (.d8 0xcc))).toInstrSpec (mov_m16_r16_effect_step 0x1294ea 2 (.base 5 (.d8 0xcc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1294ee [0x66, 0x89, 0x75, 0xCE] (StorePre 0x1294ee 4 (fun s => AddrMode.addr (.base 5 (.d8 0xce)) s (0x1294ee + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1294ee 4 6 (.base 5 (.d8 0xce)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM16R16Effect_footprint 0x1294ee 4 6 (.base 5 (.d8 0xce))).toInstrSpec (mov_m16_r16_effect_step 0x1294ee 6 (.base 5 (.d8 0xce)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x1294e3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x1294e7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x1294ea) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x1294ee) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x1294f2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l1294e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1294e0 :=
  Rest.liftedBlock (rest_l1294e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1294e0 x hx)

theorem rest_l1294f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1294f2 bytes_l1294f2) (entryMap (live .l1294f2))
      5 0x1294f2 bytes_l1294f2 b_l1294f2 := by
  have f0 : InstrSpec 0x1294f2 [0x4C, 0x89, 0x75, 0xB8] (StorePre 0x1294f2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x1294f2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1294f2 14 (.base 5 (.d8 0xb8)))
      [.gpr 14, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1294f2 14 (.base 5 (.d8 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x1294f2 0x4c (by decide) 6 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1294f6 [0x48, 0x8B, 0x4D, 0xB0] (LoadPre 0x1294f6 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x1294f6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1294f6 1 (.base 5 (.d8 0xb0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1294f6 1 (.base 5 (.d8 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x1294f6 0x48 (by decide) 1 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1294fa [0x48, 0x89, 0x4D, 0xC0] (StorePre 0x1294fa 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x1294fa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1294fa 1 (.base 5 (.d8 0xc0)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1294fa 1 (.base 5 (.d8 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x1294fa 0x48 (by decide) 1 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1294fe [0x48, 0x8B, 0x3C, 0x03] (LoadPre 0x1294fe (fun s => AddrMode.addr (.sib 3 (some 0) 0 .none) s (0x1294fe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1294fe 7 (.sib 3 (some 0) 0 .none))
      [.gpr 3, .gpr 0] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1294fe 7 (.sib 3 (some 0) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1294fe 0x48 (by decide) 7 (.sib 3 (some 0) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x129502 [0x48, 0x8D, 0x75, 0xB8] (fun s => s.RIP = 0x129502) (leaR64Effect 0x129502 6 (.base 5 (.d8 0xb8)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129502 6 (.base 5 (.d8 0xb8))).toInstrSpec (lea_r64_effect_step 0x129502 0x48 (by decide) 6 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (5, 5), (14, 14)]) (p' := 0x1294f6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (3, 3), (5, 5), (14, 14)]) (p' := 0x1294fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 54), (3, 3), (5, 5), (14, 14)]) (p' := 0x1294fe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 54), (3, 3), (5, 5), (14, 14)]) (p' := 0x129502) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 54), (3, 3), (5, 5), (14, 14)]) (p' := 0x129506) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1294f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1294f2 :=
  Rest.liftedBlock (rest_l1294f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1294f2 x hx)

theorem rest_l12950a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12950a bytes_l12950a) (entryMap (live .l12950a))
      2 0x12950a bytes_l12950a b_l12950a := by
  have f0 : InstrSpec 0x12950a [0x84, 0xC0] (fun s => s.RIP = 0x12950a) (testR8R8Effect 0x12950a 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x12950a 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x12950a 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12950c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12950c 5 0x41) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12950a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12950a :=
  Rest.liftedBlock (rest_l12950a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12950a x hx)

theorem rest_l12950e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12950e bytes_l12950e) (entryMap (live .l12950e))
      3 0x12950e bytes_l12950e b_l12950e := by
  have f0 : InstrSpec 0x12950e [0x49, 0xFF, 0xC7] (fun s => s.RIP = 0x12950e) (incR64Effect 0x12950e 15)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (incR64Effect_footprint 0x12950e 15).toInstrSpec (inc_r64_effect_step 0x12950e 0x49 0xc7 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129511 [0x4C, 0x89, 0x7D, 0xD0] (StorePre 0x129511 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129511 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129511 15 (.base 5 (.d8 0xd0)))
      [.gpr 15, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129511 15 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x129511 0x4c (by decide) 7 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129511) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129515) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 56) (jmp_rel32_effect_step 0x129515 0xfffffed6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12950e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12950e :=
  Rest.liftedBlock (rest_l12950e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12950e x hx)

theorem rest_l12951a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12951a bytes_l12951a) (entryMap (live .l12951a))
      5 0x12951a bytes_l12951a b_l12951a := by
  have f0 : InstrSpec 0x12951a [0x0F, 0xB7, 0xD2] (fun s => s.RIP = 0x12951a) (movzxR32R16Effect 0x12951a 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R16Effect_footprint 0x12951a 3 2 2).toInstrSpec (movzx_r32_r16_effect_step 0x12951a 0xd2 (by decide)) pre_rip
  have f1 : InstrSpec 0x12951d [0xC1, 0xE2, 0x04] (fun s => s.RIP = 0x12951d) (shlR32Effect 0x12951d 3 2 4)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x12951d 3 2 4).toInstrSpec (shl_r32_imm8_effect_step 0x12951d 0xe2 0x4 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129520 [0x0F, 0xB7, 0x54, 0x13, 0x08] (LoadPre 0x129520 (fun s => AddrMode.addr (.sib 3 (some 2) 0 (.d8 0x8)) s (0x129520 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x129520 5 2 (.sib 3 (some 2) 0 (.d8 0x8)))
      [.gpr 3, .gpr 2] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x129520 5 2 (.sib 3 (some 2) 0 (.d8 0x8))).toInstrSpec (movzx_r32_m16_effect_step 0x129520 2 (.sib 3 (some 2) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x129525 [0xA8, 0x20] (fun s => s.RIP = 0x129525) (testAlImm8Effect 0x129525 0x20)
      [.gpr 0] [] [.flags, .rip] :=
    (testAlImm8Effect_footprint 0x129525 0x20).toInstrSpec (test_al_imm8_effect_step 0x129525 0x20) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x12951d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x129520) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)]) (p' := 0x129525) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15), (19, 59)]) (p' := 0x129527) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x129527 5 0xac) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12951a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12951a :=
  Rest.liftedBlock (rest_l12951a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12951a x hx)

theorem rest_l129529 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129529 bytes_l129529) (entryMap (live .l129529))
      1 0x129529 bytes_l129529 b_l129529 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x129529 0xb5 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l129529 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129529 :=
  Rest.liftedBlock (rest_l129529 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129529 x hx)

theorem rest_l12952b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12952b bytes_l12952b) (entryMap (live .l12952b))
      12 0x12952b bytes_l12952b b_l12952b := by
  have f0 : InstrSpec 0x12952b [0x48, 0xD1, 0xEB] (fun s => s.RIP = 0x12952b) (shrR64Effect 0x12952b 3 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x12952b 3 3 1).toInstrSpec (shr_r64_one_effect_step 0x12952b 0x48 0xeb (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12952e [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x12952e (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12952e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12952e 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12952e 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12952e 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x129532 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x129532) (movR64R64Effect 0x129532 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129532 7 14).toInstrSpec (mov_r64_r64_effect_step 0x129532 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129535 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x129535) (movR64R64Effect 0x129535 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x129535 6 13).toInstrSpec (mov_r64_r64_effect_step 0x129535 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129538 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x129538) (movR64R64Effect 0x129538 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129538 2 3).toInstrSpec (mov_r64_r64_effect_step 0x129538 0x48 0xda (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12953b [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x12953b) (addR64Imm8Effect 0x12953b 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12953b 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x12953b 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12953f [0x5B] (PopPre 0x12953f) (popR64Effect 0x12953f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12953f 1 3).toInstrSpec (pop_r64_effect_step 0x12953f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x129540 [0x41, 0x5C] (PopPre 0x129540) (popR64Effect 0x129540 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129540 2 12).toInstrSpec (pop_r64_rex_effect_step 0x129540 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x129542 [0x41, 0x5D] (PopPre 0x129542) (popR64Effect 0x129542 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129542 2 13).toInstrSpec (pop_r64_rex_effect_step 0x129542 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x129544 [0x41, 0x5E] (PopPre 0x129544) (popR64Effect 0x129544 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129544 2 14).toInstrSpec (pop_r64_rex_effect_step 0x129544 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x129546 [0x41, 0x5F] (PopPre 0x129546) (popR64Effect 0x129546 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129546 2 15).toInstrSpec (pop_r64_rex_effect_step 0x129546 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x129548 [0x5D] (PopPre 0x129548) (popR64Effect 0x129548 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129548 1 5).toInstrSpec (pop_r64_effect_step 0x129548 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (6, 6), (13, 13), (14, 14)]) (p' := 0x12952e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 53), (4, 4), (6, 6), (13, 13), (14, 14)]) (p' := 0x129532) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (6, 6), (13, 13), (14, 14)]) (p' := 0x129535) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 53), (4, 4), (13, 13), (14, 14)]) (p' := 0x129538) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 53), (4, 4), (13, 13), (14, 14)]) (p' := 0x12953b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 53), (4, 59), (13, 13), (14, 14)]) (p' := 0x12953f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 61), (13, 13), (14, 14)]) (p' := 0x129540) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(4, 63), (13, 13), (14, 14)]) (p' := 0x129542) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(4, 65), (14, 14)]) (p' := 0x129544) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(4, 67)]) (p' := 0x129546) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(4, 69)]) (p' := 0x129548) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := []) (p' := 0x129549) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12952b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12952b :=
  Rest.liftedBlock (rest_l12952b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12952b x hx)

theorem rest_l12954b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12954b bytes_l12954b) (entryMap (live .l12954b))
      2 0x12954b bytes_l12954b b_l12954b := by
  have f0 : InstrSpec 0x12954b [0x31, 0xC0] (fun s => s.RIP = 0x12954b) (xorR32R32Effect 0x12954b 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12954b 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12954b 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12954d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x12954d 0x2 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12954b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12954b :=
  Rest.liftedBlock (rest_l12954b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12954b x hx)

theorem rest_l12954f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12954f bytes_l12954f) (entryMap (live .l12954f))
      1 0x12954f bytes_l12954f b_l12954f := by
  have f0 : InstrSpec 0x12954f [0xB0, 0x01] (fun s => s.RIP = 0x12954f) (movR8Imm8Effect 0x12954f 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x12954f 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x12954f 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129551) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l12954f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12954f :=
  Rest.liftedBlock (rest_l12954f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12954f x hx)

theorem rest_l129551 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129551 bytes_l129551) (entryMap (live .l129551))
      8 0x129551 bytes_l129551 b_l129551 := by
  have f0 : InstrSpec 0x129551 [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x129551) (addR64Imm8Effect 0x129551 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129551 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x129551 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129555 [0x5B] (PopPre 0x129555) (popR64Effect 0x129555 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129555 1 3).toInstrSpec (pop_r64_effect_step 0x129555 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129556 [0x41, 0x5C] (PopPre 0x129556) (popR64Effect 0x129556 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129556 2 12).toInstrSpec (pop_r64_rex_effect_step 0x129556 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129558 [0x41, 0x5D] (PopPre 0x129558) (popR64Effect 0x129558 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129558 2 13).toInstrSpec (pop_r64_rex_effect_step 0x129558 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x12955a [0x41, 0x5E] (PopPre 0x12955a) (popR64Effect 0x12955a 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12955a 2 14).toInstrSpec (pop_r64_rex_effect_step 0x12955a 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x12955c [0x41, 0x5F] (PopPre 0x12955c) (popR64Effect 0x12955c 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12955c 2 15).toInstrSpec (pop_r64_rex_effect_step 0x12955c 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12955e [0x5D] (PopPre 0x12955e) (popR64Effect 0x12955e 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12955e 1 5).toInstrSpec (pop_r64_effect_step 0x12955e 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x12955f [0xC3] (RetPre 0x12955f) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12955f).toInstrSpec (ret_effect_step 0x12955f) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129555) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129556) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129558) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12955a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12955c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12955e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12955f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l129551 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129551 :=
  Rest.liftedBlock (rest_l129551 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129551 x hx)

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

theorem_by block_l1293a0_eval :
    program.runBlock (dialect code) ⟨.l1293a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1293c3_eval :
    program.runBlock (dialect code) ⟨.l1293c3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1293d0_eval :
    program.runBlock (dialect code) ⟨.l1293d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1293f0_eval :
    program.runBlock (dialect code) ⟨.l1293f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129400_eval :
    program.runBlock (dialect code) ⟨.l129400, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12940c_eval :
    program.runBlock (dialect code) ⟨.l12940c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129418_eval :
    program.runBlock (dialect code) ⟨.l129418, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129420_eval :
    program.runBlock (dialect code) ⟨.l129420, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129430_eval :
    program.runBlock (dialect code) ⟨.l129430, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129434_eval :
    program.runBlock (dialect code) ⟨.l129434, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12943d_eval :
    program.runBlock (dialect code) ⟨.l12943d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129455_eval :
    program.runBlock (dialect code) ⟨.l129455, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129467_eval :
    program.runBlock (dialect code) ⟨.l129467, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12946f_eval :
    program.runBlock (dialect code) ⟨.l12946f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12947c_eval :
    program.runBlock (dialect code) ⟨.l12947c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129485_eval :
    program.runBlock (dialect code) ⟨.l129485, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129490_eval :
    program.runBlock (dialect code) ⟨.l129490, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129494_eval :
    program.runBlock (dialect code) ⟨.l129494, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12949e_eval :
    program.runBlock (dialect code) ⟨.l12949e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1294ab_eval :
    program.runBlock (dialect code) ⟨.l1294ab, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1294ad_eval :
    program.runBlock (dialect code) ⟨.l1294ad, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1294be_eval :
    program.runBlock (dialect code) ⟨.l1294be, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1294c4_eval :
    program.runBlock (dialect code) ⟨.l1294c4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1294cd_eval :
    program.runBlock (dialect code) ⟨.l1294cd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1294d1_eval :
    program.runBlock (dialect code) ⟨.l1294d1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1294d5_eval :
    program.runBlock (dialect code) ⟨.l1294d5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1294e0_eval :
    program.runBlock (dialect code) ⟨.l1294e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1294f2_eval :
    program.runBlock (dialect code) ⟨.l1294f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12950a_eval :
    program.runBlock (dialect code) ⟨.l12950a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12950e_eval :
    program.runBlock (dialect code) ⟨.l12950e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12951a_eval :
    program.runBlock (dialect code) ⟨.l12951a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129529_eval :
    program.runBlock (dialect code) ⟨.l129529, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12952b_eval :
    program.runBlock (dialect code) ⟨.l12952b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12954b_eval :
    program.runBlock (dialect code) ⟨.l12954b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12954f_eval :
    program.runBlock (dialect code) ⟨.l12954f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129551_eval :
    program.runBlock (dialect code) ⟨.l129551, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Sec1.LIR
