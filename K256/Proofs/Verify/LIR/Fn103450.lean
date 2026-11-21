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

theorem rest_l103450 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103450 bytes_l103450) (entryMap (live .l103450))
      9 0x103450 bytes_l103450 b_l103450 := by
  have f0 : InstrSpec 0x103450 [0x41, 0x57] (PushPre 0x103450 2) (pushR64Effect 0x103450 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103450 2 15).toInstrSpec (push_r64_rex_effect_step 0x103450 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103452 [0x41, 0x56] (PushPre 0x103452 2) (pushR64Effect 0x103452 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103452 2 14).toInstrSpec (push_r64_rex_effect_step 0x103452 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103454 [0x53] (PushPre 0x103454 1) (pushR64Effect 0x103454 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103454 1 3).toInstrSpec (push_r64_effect_step 0x103454 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103455 [0x48, 0x81, 0xEC, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103455) (subR64Imm32Effect 0x103455 4 0xc0)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x103455 4 0xc0).toInstrSpec (sub_r64_imm32_effect_step 0x103455 0x48 0xec 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10345c [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x10345c) (movR64R64Effect 0x10345c 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10345c 14 2).toInstrSpec (mov_r64_r64_effect_step 0x10345c 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10345f [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10345f) (movR64R64Effect 0x10345f 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10345f 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10345f 0x48 0xfb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103462 [0x4C, 0x8D, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103462) (leaR64Effect 0x103462 15 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x103462 15 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x103462 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10346a [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10346a) (movR64R64Effect 0x10346a 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10346a 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10346a 0x4c 0xff (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10346d [0xE8, 0x4E, 0x8F, 0x01, 0x00] (PushPre 0x10346d 5) (callEffect (fun _ => 0x11c3c0) 0x103472)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10346d 0x11c3c0 0x103472).toInstrSpec (call_rel32_effect_step 0x10346d 0x18f4e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103452) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103454) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103455) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10345c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10345f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103462) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10346a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 63), (4, 59), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10346d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 63), (4, 69), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3c0) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l103450 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103450 :=
  Rest.liftedBlock (rest_l103450 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103450 x hx)

theorem rest_l103472 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103472 bytes_l103472) (entryMap (live .l103472))
      4 0x103472 bytes_l103472 b_l103472 := by
  have f0 : InstrSpec 0x103472 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x103472) (movR64R64Effect 0x103472 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103472 7 4).toInstrSpec (mov_r64_r64_effect_step 0x103472 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103475 [0xBA, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103475) (movR32Imm32Effect 0x103475 5 2 0x20)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x103475 5 2 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x103475 0xba (by decide) 0x20) pre_rip
  have f2 : InstrSpec 0x10347a [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x10347a) (movR64R64Effect 0x10347a 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10347a 6 15).toInstrSpec (mov_r64_r64_effect_step 0x10347a 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10347d [0xE8, 0xAE, 0x42, 0x00, 0x00] (PushPre 0x10347d 5) (callEffect (fun _ => 0x107730) 0x103482)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10347d 0x107730 0x103482).toInstrSpec (call_rel32_effect_step 0x10347d 0x42ae (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103475) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10347a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10347d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107730) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l103472 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103472 :=
  Rest.liftedBlock (rest_l103472 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103472 x hx)

theorem rest_l103482 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103482 bytes_l103482) (entryMap (live .l103482))
      2 0x103482 bytes_l103482 b_l103482 := by
  have f0 : InstrSpec 0x103482 [0x83, 0x3C, 0x24, 0x01] (LoadPre 0x103482 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103482 + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x103482 4 32 (.sib 4 none 0 .none) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x103482 4 (.sib 4 none 0 .none) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x103482 (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103486) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x103486 4 0x141) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103482 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103482 :=
  Rest.liftedBlock (rest_l103482 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103482 x hx)

theorem rest_l10348c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10348c bytes_l10348c) (entryMap (live .l10348c))
      20 0x10348c bytes_l10348c b_l10348c := by
  have f0 : InstrSpec 0x10348c [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10348c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10348c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10348c 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10348c 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10348c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103491 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x103491 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103491 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103491 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103491 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103491 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x103496 [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x103496 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103496 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103496 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103496 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x103496 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10349b [0x48, 0x89, 0x54, 0x24, 0x50] (StorePre 0x10349b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10349b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10349b 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10349b 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10349b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1034a0 [0x48, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x1034a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1034a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1034a0 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1034a0 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1034a0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1034a5 [0x48, 0x89, 0x54, 0x24, 0x58] (StorePre 0x1034a5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1034a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1034a5 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1034a5 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1034a5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1034aa [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x1034aa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1034aa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1034aa 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1034aa 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1034aa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1034af [0x48, 0x89, 0x4C, 0x24, 0x48] (StorePre 0x1034af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1034af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1034af 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1034af 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1034af 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1034b4 [0x49, 0x8B, 0x46, 0x18] (LoadPre 0x1034b4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1034b4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034b4 0 (.base 14 (.d8 0x18)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1034b4 0 (.base 14 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1034b4 0x49 (by decide) 0 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1034b8 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1034b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1034b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1034b8 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1034b8 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x1034b8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1034c0 [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x1034c0 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1034c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034c0 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1034c0 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1034c0 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1034c4 [0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1034c4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1034c4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1034c4 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1034c4 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1034c4 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1034cc [0x49, 0x8B, 0x06] (LoadPre 0x1034cc (fun s => AddrMode.addr (.base 14 .none) s (0x1034cc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1034cc 0 (.base 14 .none))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1034cc 0 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1034cc 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1034cf [0x49, 0x8B, 0x4E, 0x08] (LoadPre 0x1034cf (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1034cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034cf 1 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1034cf 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1034cf 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1034d3 [0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1034d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1034d3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1034d3 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1034d3 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1034d3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1034db [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1034db 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1034db + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1034db 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1034db 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1034db 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1034e3 [0x4C, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1034e3) (leaR64Effect 0x1034e3 14 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x1034e3 14 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x1034e3 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1034eb [0x48, 0x8D, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1034eb) (leaR64Effect 0x1034eb 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1034eb 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x1034eb 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1034f3 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1034f3) (movR64R64Effect 0x1034f3 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1034f3 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1034f3 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1034f6 [0xE8, 0xC5, 0x8E, 0x01, 0x00] (PushPre 0x1034f6 5) (callEffect (fun _ => 0x11c3c0) 0x1034fb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1034f6 0x11c3c0 0x1034fb).toInstrSpec (call_rel32_effect_step 0x1034f6 0x18ec5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103491) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103496) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10349b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034a0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034a5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034aa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034af) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034b4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034b8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c0) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034cc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034cf) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034d3) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034db) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034e3) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034eb) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (6, 79), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034f3) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 4), (5, 5), (6, 79), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034f6) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 73), (2, 60), (3, 3), (4, 83), (5, 5), (6, 79), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3c0) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l10348c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10348c :=
  Rest.liftedBlock (rest_l10348c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10348c x hx)

theorem rest_l1034fb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1034fb bytes_l1034fb) (entryMap (live .l1034fb))
      4 0x1034fb bytes_l1034fb b_l1034fb := by
  have f0 : InstrSpec 0x1034fb [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1034fb) (movR64R64Effect 0x1034fb 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1034fb 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1034fb 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1034fe [0xBA, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1034fe) (movR32Imm32Effect 0x1034fe 5 2 0x20)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1034fe 5 2 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x1034fe 0xba (by decide) 0x20) pre_rip
  have f2 : InstrSpec 0x103503 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x103503) (movR64R64Effect 0x103503 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103503 6 14).toInstrSpec (mov_r64_r64_effect_step 0x103503 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103506 [0xE8, 0x25, 0x42, 0x00, 0x00] (PushPre 0x103506 5) (callEffect (fun _ => 0x107730) 0x10350b)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103506 0x107730 0x10350b).toInstrSpec (call_rel32_effect_step 0x103506 0x4225 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103503) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103506) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107730) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1034fb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1034fb :=
  Rest.liftedBlock (rest_l1034fb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1034fb x hx)

theorem rest_l10350b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10350b bytes_l10350b) (entryMap (live .l10350b))
      2 0x10350b bytes_l10350b b_l10350b := by
  have f0 : InstrSpec 0x10350b [0x83, 0x3C, 0x24, 0x01] (LoadPre 0x10350b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10350b + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x10350b 4 32 (.sib 4 none 0 .none) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x10350b 4 (.sib 4 none 0 .none) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x10350b (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10350f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10350f 4 0xb8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10350b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10350b :=
  Rest.liftedBlock (rest_l10350b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10350b x hx)

theorem rest_l103515 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103515 bytes_l103515) (entryMap (live .l103515))
      17 0x103515 bytes_l103515 b_l103515 := by
  have f0 : InstrSpec 0x103515 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x103515 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103515 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103515 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103515 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x103515 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10351a [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x10351a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10351a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10351a 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10351a 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10351a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10351f [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x10351f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10351f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10351f 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10351f 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10351f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103524 [0x48, 0x89, 0x54, 0x24, 0x70] (StorePre 0x103524 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x103524 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103524 2 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103524 2 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x103524 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103529 [0x48, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x103529 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103529 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103529 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103529 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103529 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10352e [0x48, 0x89, 0x54, 0x24, 0x78] (StorePre 0x10352e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10352e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10352e 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10352e 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x10352e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103533 [0x48, 0x89, 0x44, 0x24, 0x60] (StorePre 0x103533 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103533 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103533 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103533 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x103533 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x103538 [0x48, 0x89, 0x4C, 0x24, 0x68] (StorePre 0x103538 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x103538 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103538 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103538 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x103538 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10353d [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10353d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10353d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10353d (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10353d (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10353d 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x103546 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103546 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103546 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103546 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103546 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103546 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10354f [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10354f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10354f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10354f (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10354f (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10354f 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x103558 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103558 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103558 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x103558 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103558 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103558 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103560 [0x48, 0x8D, 0x7C, 0x24, 0x40] (fun s => s.RIP = 0x103560) (leaR64Effect 0x103560 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103560 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x103560 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x103565 [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x103565) (movR64R64Effect 0x103565 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103565 2 4).toInstrSpec (mov_r64_r64_effect_step 0x103565 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x103568 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103568) (movR32Imm32Effect 0x103568 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x103568 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x103568 0xbe (by decide) 0x4) pre_rip
  have f15 : InstrSpec 0x10356d [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10356d) (movR32Imm32Effect 0x10356d 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10356d 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10356d 0xb9 (by decide) 0x4) pre_rip
  have f16 : InstrSpec 0x103572 [0xE8, 0xD9, 0x49, 0x02, 0x00] (PushPre 0x103572 5) (callEffect (fun _ => 0x127f50) 0x103577)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103572 0x127f50 0x103577).toInstrSpec (call_rel32_effect_step 0x103572 0x249d9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10351a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10351f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103524) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103529) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10352e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103533) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103538) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10353d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103546) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10354f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103558) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103560) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 55), (2, 60), (3, 3), (4, 4), (5, 5), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103565) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 55), (2, 71), (3, 3), (4, 4), (5, 5), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103568) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 55), (2, 71), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10356d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 75), (2, 71), (3, 3), (4, 4), (5, 5), (6, 73), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103572) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 75), (2, 71), (3, 3), (4, 77), (5, 5), (6, 73), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 79) (by decide) (by decide) rfl rfl

theorem block_l103515 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103515 :=
  Rest.liftedBlock (rest_l103515 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103515 x hx)

theorem rest_l103577 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103577 bytes_l103577) (entryMap (live .l103577))
      3 0x103577 bytes_l103577 b_l103577 := by
  have f0 : InstrSpec 0x103577 [0x24, 0x01] (fun s => s.RIP = 0x103577) (andAlImm8Effect 0x103577 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x103577 0x1).toInstrSpec (and_al_imm8_effect_step 0x103577 0x1) pre_rip
  have f1 : InstrSpec 0x103579 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x103579) (movzxR32R8Effect 0x103579 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x103579 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x103579 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10357c [0xE8, 0xCF, 0x47, 0x02, 0x00] (PushPre 0x10357c 5) (callEffect (fun _ => 0x127d50) 0x103581)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10357c 0x127d50 0x103581).toInstrSpec (call_rel32_effect_step 0x10357c 0x247cf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103579) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10357c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l103577 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103577 :=
  Rest.liftedBlock (rest_l103577 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103577 x hx)

theorem rest_l103581 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103581 bytes_l103581) (entryMap (live .l103581))
      2 0x103581 bytes_l103581 b_l103581 := by
  have f0 : InstrSpec 0x103581 [0x84, 0xC0] (fun s => s.RIP = 0x103581) (testR8R8Effect 0x103581 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x103581 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x103581 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103583) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x103583 5 0x48) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103581 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103581 :=
  Rest.liftedBlock (rest_l103581 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103581 x hx)

theorem rest_l103585 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103585 bytes_l103585) (entryMap (live .l103585))
      9 0x103585 bytes_l103585 b_l103585 := by
  have f0 : InstrSpec 0x103585 [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103585 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x103585 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103585 (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103585 (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103585 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10358e [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10358e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10358e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10358e (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10358e (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10358e 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103597 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103597 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103597 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103597 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103597 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103597 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1035a0 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1035a0 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1035a0 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1035a0 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1035a0 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1035a0 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1035a8 [0x48, 0x8D, 0x7C, 0x24, 0x60] (fun s => s.RIP = 0x1035a8) (leaR64Effect 0x1035a8 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1035a8 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x1035a8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1035ad [0x48, 0x89, 0xE2] (fun s => s.RIP = 0x1035ad) (movR64R64Effect 0x1035ad 2 4)
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1035ad 2 4).toInstrSpec (mov_r64_r64_effect_step 0x1035ad 0x48 0xe2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1035b0 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1035b0) (movR32Imm32Effect 0x1035b0 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1035b0 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x1035b0 0xbe (by decide) 0x4) pre_rip
  have f7 : InstrSpec 0x1035b5 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1035b5) (movR32Imm32Effect 0x1035b5 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1035b5 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x1035b5 0xb9 (by decide) 0x4) pre_rip
  have f8 : InstrSpec 0x1035ba [0xE8, 0x91, 0x49, 0x02, 0x00] (PushPre 0x1035ba 5) (callEffect (fun _ => 0x127f50) 0x1035bf)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1035ba 0x127f50 0x1035bf).toInstrSpec (call_rel32_effect_step 0x1035ba 0x24991 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10358e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103597) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035a0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035a8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035ad) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035b0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035b5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035ba) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 59), (3, 3), (4, 65), (5, 5), (6, 61), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l103585 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103585 :=
  Rest.liftedBlock (rest_l103585 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103585 x hx)

theorem rest_l1035bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035bf bytes_l1035bf) (entryMap (live .l1035bf))
      3 0x1035bf bytes_l1035bf b_l1035bf := by
  have f0 : InstrSpec 0x1035bf [0x24, 0x01] (fun s => s.RIP = 0x1035bf) (andAlImm8Effect 0x1035bf 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x1035bf 0x1).toInstrSpec (and_al_imm8_effect_step 0x1035bf 0x1) pre_rip
  have f1 : InstrSpec 0x1035c1 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x1035c1) (movzxR32R8Effect 0x1035c1 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x1035c1 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x1035c1 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1035c4 [0xE8, 0x87, 0x47, 0x02, 0x00] (PushPre 0x1035c4 5) (callEffect (fun _ => 0x127d50) 0x1035c9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1035c4 0x127d50 0x1035c9).toInstrSpec (call_rel32_effect_step 0x1035c4 0x24787 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1035bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035bf :=
  Rest.liftedBlock (rest_l1035bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035bf x hx)

theorem rest_l1035c9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035c9 bytes_l1035c9) (entryMap (live .l1035c9))
      2 0x1035c9 bytes_l1035c9 b_l1035c9 := by
  have f0 : InstrSpec 0x1035c9 [0x84, 0xC0] (fun s => s.RIP = 0x1035c9) (testR8R8Effect 0x1035c9 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1035c9 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1035c9 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035cb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1035cb 4 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1035c9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035c9 :=
  Rest.liftedBlock (rest_l1035c9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035c9 x hx)

theorem rest_l1035cd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035cd bytes_l1035cd) (entryMap (live .l1035cd))
      2 0x1035cd bytes_l1035cd b_l1035cd := by
  have f0 : InstrSpec 0x1035cd [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1035cd 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1035cd + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1035cd (.base 3 (.d8 0x8)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1035cd (.base 3 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1035cd 0x48 (by decide) (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1035d5 [0x48, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1035d5 7 (fun s => AddrMode.addr (.base 3 .none) s (0x1035d5 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x1035d5 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1035d5 (.base 3 .none) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x1035d5 0x48 (by decide) (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035d5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035dc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1035cd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035cd :=
  Rest.liftedBlock (rest_l1035cd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035cd x hx)

theorem rest_l1035dc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035dc bytes_l1035dc) (entryMap (live .l1035dc))
      6 0x1035dc bytes_l1035dc b_l1035dc := by
  have f0 : InstrSpec 0x1035dc [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1035dc) (movR64R64Effect 0x1035dc 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1035dc 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1035dc 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1035df [0x48, 0x81, 0xC4, 0xC0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1035df) (addR64Imm32Effect 0x1035df 4 0xc0)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1035df 4 0xc0).toInstrSpec (add_r64_imm32_effect_step 0x1035df 0x48 0xc4 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1035e6 [0x5B] (PopPre 0x1035e6) (popR64Effect 0x1035e6 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1035e6 1 3).toInstrSpec (pop_r64_effect_step 0x1035e6 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1035e7 [0x41, 0x5E] (PopPre 0x1035e7) (popR64Effect 0x1035e7 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1035e7 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1035e7 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1035e9 [0x41, 0x5F] (PopPre 0x1035e9) (popR64Effect 0x1035e9 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1035e9 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1035e9 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1035eb [0xC3] (RetPre 0x1035eb) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1035eb).toInstrSpec (ret_effect_step 0x1035eb) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035df) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035e6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035e7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035e9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035eb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l1035dc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035dc :=
  Rest.liftedBlock (rest_l1035dc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035dc x hx)

theorem rest_l1035ec_1 [Bindings] (code : CodeMap) :
    Rest (n := 81) code lifted (codeRange 0x1035ec bytes_l1035ec) [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x10364b bytes_l1035ec_1 b_l1035ec_1 := by
  have f20 : InstrSpec 0x10364b [0x48, 0x89, 0x43, 0x20] (StorePre 0x10364b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10364b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10364b 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10364b 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10364b 0x48 (by decide) 0 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10364f [0x48, 0x89, 0x4B, 0x18] (StorePre 0x10364f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10364f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10364f 1 (.base 3 (.d8 0x18)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10364f 1 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10364f 0x48 (by decide) 1 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x103653 [0x48, 0x89, 0x73, 0x10] (StorePre 0x103653 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x103653 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103653 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103653 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x103653 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x103657 [0x48, 0x89, 0x53, 0x08] (StorePre 0x103657 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x103657 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103657 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103657 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x103657 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10365b [0x48, 0xC7, 0x03, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10365b 7 (fun s => AddrMode.addr (.base 3 .none) s (0x10365b + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x10365b (.base 3 .none) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10365b (.base 3 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10365b 0x48 (by decide) (.base 3 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10364f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103653) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103657) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10365b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103662) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 86) (jmp_rel32_effect_step 0x103662 0xffffff75 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l1035ec [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1035ec bytes_l1035ec) (entryMap (live .l1035ec))
      26 0x1035ec bytes_l1035ec b_l1035ec := by
  have f0 : InstrSpec 0x1035ec [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x1035ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1035ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1035ec 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1035ec 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1035ec 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1035f1 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x1035f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1035f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1035f1 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1035f1 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1035f1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1035f6 [0x48, 0x8B, 0x4C, 0x24, 0x50] (LoadPre 0x1035f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1035f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1035f6 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1035f6 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1035f6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1035fb [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x1035fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1035fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1035fb 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1035fb 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1035fb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103600 [0x48, 0x8B, 0x54, 0x24, 0x40] (LoadPre 0x103600 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103600 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103600 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x103600 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x103600 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103605 [0x48, 0x8B, 0x74, 0x24, 0x48] (LoadPre 0x103605 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103605 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103605 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x103605 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x103605 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10360a [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x10360a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10360a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10360a 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10360a 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10360a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10360f [0x48, 0x89, 0x14, 0x24] (StorePre 0x10360f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10360f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10360f 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10360f 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10360f 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103613 [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x103613 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x103613 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103613 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x103613 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x103613 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103618 [0x4C, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x103618 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x103618 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103618 8 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x103618 8 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x103618 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10361d [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x10361d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10361d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10361d 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10361d 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10361d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x103622 [0x4C, 0x89, 0x44, 0x24, 0x28] (StorePre 0x103622 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x103622 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103622 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103622 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x103622 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103627 [0x4C, 0x8B, 0x4C, 0x24, 0x70] (LoadPre 0x103627 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x103627 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103627 9 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x103627 9 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x103627 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10362c [0x4C, 0x89, 0x4C, 0x24, 0x30] (StorePre 0x10362c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10362c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10362c 9 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10362c 9 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10362c 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x103631 [0x4C, 0x8B, 0x54, 0x24, 0x78] (LoadPre 0x103631 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x103631 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103631 10 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x103631 10 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x103631 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x103636 [0x4C, 0x89, 0x54, 0x24, 0x38] (StorePre 0x103636 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103636 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103636 10 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103636 10 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x103636 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10363b [0x4C, 0x89, 0x53, 0x40] (StorePre 0x10363b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x10363b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10363b 10 (.base 3 (.d8 0x40)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10363b 10 (.base 3 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10363b 0x4c (by decide) 2 (.base 3 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10363f [0x4C, 0x89, 0x4B, 0x38] (StorePre 0x10363f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x10363f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10363f 9 (.base 3 (.d8 0x38)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10363f 9 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10363f 0x4c (by decide) 1 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x103643 [0x4C, 0x89, 0x43, 0x30] (StorePre 0x103643 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x103643 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103643 8 (.base 3 (.d8 0x30)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103643 8 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x103643 0x4c (by decide) 0 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x103647 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x103647 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x103647 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103647 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x103647 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x103647 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035f6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 56), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1035fb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 56), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103600) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103605) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10360a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10360f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103613) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103618) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10361d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103622) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103627) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10362c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103631) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103636) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10363b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10363f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103643) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103647) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 56), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 65), (8, 67), (9, 71), (10, 74), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10364b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1035ec_1 code

theorem block_l1035ec [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1035ec :=
  Rest.liftedBlock (rest_l1035ec code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1035ec x hx)

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

theorem_by block_l103450_eval :
    program.runBlock (dialect code) ⟨.l103450, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103472_eval :
    program.runBlock (dialect code) ⟨.l103472, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103482_eval :
    program.runBlock (dialect code) ⟨.l103482, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10348c_eval :
    program.runBlock (dialect code) ⟨.l10348c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1034fb_eval :
    program.runBlock (dialect code) ⟨.l1034fb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10350b_eval :
    program.runBlock (dialect code) ⟨.l10350b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103515_eval :
    program.runBlock (dialect code) ⟨.l103515, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103577_eval :
    program.runBlock (dialect code) ⟨.l103577, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103581_eval :
    program.runBlock (dialect code) ⟨.l103581, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103585_eval :
    program.runBlock (dialect code) ⟨.l103585, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035bf_eval :
    program.runBlock (dialect code) ⟨.l1035bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035c9_eval :
    program.runBlock (dialect code) ⟨.l1035c9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035cd_eval :
    program.runBlock (dialect code) ⟨.l1035cd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035dc_eval :
    program.runBlock (dialect code) ⟨.l1035dc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1035ec_eval :
    program.runBlock (dialect code) ⟨.l1035ec, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
