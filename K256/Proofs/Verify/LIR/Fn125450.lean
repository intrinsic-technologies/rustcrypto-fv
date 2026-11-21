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

theorem rest_l125450 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125450 bytes_l125450) (entryMap (live .l125450))
      11 0x125450 bytes_l125450 b_l125450 := by
  have f0 : InstrSpec 0x125450 [0x55] (PushPre 0x125450 1) (pushR64Effect 0x125450 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125450 1 5).toInstrSpec (push_r64_effect_step 0x125450 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x125451 [0x41, 0x57] (PushPre 0x125451 2) (pushR64Effect 0x125451 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125451 2 15).toInstrSpec (push_r64_rex_effect_step 0x125451 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x125453 [0x41, 0x56] (PushPre 0x125453 2) (pushR64Effect 0x125453 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125453 2 14).toInstrSpec (push_r64_rex_effect_step 0x125453 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x125455 [0x41, 0x55] (PushPre 0x125455 2) (pushR64Effect 0x125455 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125455 2 13).toInstrSpec (push_r64_rex_effect_step 0x125455 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x125457 [0x41, 0x54] (PushPre 0x125457 2) (pushR64Effect 0x125457 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125457 2 12).toInstrSpec (push_r64_rex_effect_step 0x125457 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x125459 [0x53] (PushPre 0x125459 1) (pushR64Effect 0x125459 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125459 1 3).toInstrSpec (push_r64_effect_step 0x125459 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12545a [0x48, 0x83, 0xEC, 0x78] (fun s => s.RIP = 0x12545a) (subR64Imm8Effect 0x12545a 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x12545a 4 0x78).toInstrSpec (sub_r64_imm8_effect_step 0x12545a 0x48 0xec 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12545e [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x12545e) (movR64R64Effect 0x12545e 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x12545e 14 6).toInstrSpec (mov_r64_r64_effect_step 0x12545e 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x125461 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x125461) (movR64R64Effect 0x125461 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x125461 3 7).toInstrSpec (mov_r64_r64_effect_step 0x125461 0x48 0xfb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x125464 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x125464) (leaR64Effect 0x125464 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x125464 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x125464 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x125469 [0xE8, 0xC2, 0xEF, 0xFF, 0xFF] (PushPre 0x125469 5) (callEffect (fun _ => 0x124430) 0x12546e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x125469 0x124430 0x12546e).toInstrSpec (call_rel32_effect_step 0x125469 0xffffefc2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125451) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125453) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125455) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125457) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125459) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12545a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12545e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125461) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125464) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(3, 69), (4, 65), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125469) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(3, 69), (4, 73), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124430) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l125450 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125450 :=
  Rest.liftedBlock (rest_l125450 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125450 x hx)

theorem rest_l12546e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12546e bytes_l12546e) (entryMap (live .l12546e))
      3 0x12546e bytes_l12546e b_l12546e := by
  have f0 : InstrSpec 0x12546e [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x12546e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12546e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12546e 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x12546e 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x12546e 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125472 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x125472) (cmpR32Imm8Effect 0x125472 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x125472 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x125472 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125472) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125475) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x125475 5 0x7c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12546e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12546e :=
  Rest.liftedBlock (rest_l12546e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12546e x hx)

theorem rest_l125477 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125477 bytes_l125477) (entryMap (live .l125477))
      8 0x125477 bytes_l125477 b_l125477 := by
  have f0 : InstrSpec 0x125477 [0x44, 0x8B, 0x64, 0x24, 0x0C] (LoadPre 0x125477 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125477 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125477 12 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x125477 12 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_effect_step 0x125477 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12547c [0x44, 0x8B, 0x6C, 0x24, 0x10] (LoadPre 0x12547c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12547c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x12547c 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x12547c 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x12547c 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125481 [0x4C, 0x8B, 0x7C, 0x24, 0x0C] (LoadPre 0x125481 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x125481 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125481 15 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x125481 15 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x125481 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125486 [0x0F, 0xB6, 0x6C, 0x24, 0x14] (LoadPre 0x125486 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125486 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125486 5 5 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x125486 5 5 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m8_effect_step 0x125486 5 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12548b [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x12548b) (leaR64Effect 0x12548b 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12548b 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x12548b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x125490 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x125490) (movR64R64Effect 0x125490 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x125490 6 14).toInstrSpec (mov_r64_r64_effect_step 0x125490 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x125493 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125493) (movR32Imm32Effect 0x125493 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x125493 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x125493 0xba (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x125498 [0xE8, 0xE3, 0x26, 0x00, 0x00] (PushPre 0x125498 5) (callEffect (fun _ => 0x127b80) 0x12549d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x125498 0x127b80 0x12549d).toInstrSpec (call_rel32_effect_step 0x125498 0x26e3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12547c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125481) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125486) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12548b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 59), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125490) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 59), (6, 63), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125493) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 65), (3, 3), (4, 4), (5, 59), (6, 63), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125498) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 65), (3, 3), (4, 67), (5, 59), (6, 63), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 55), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l125477 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125477 :=
  Rest.liftedBlock (rest_l125477 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125477 x hx)

theorem rest_l12549d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12549d bytes_l12549d) (entryMap (live .l12549d))
      3 0x12549d bytes_l12549d b_l12549d := by
  have f0 : InstrSpec 0x12549d [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x12549d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12549d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12549d 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x12549d 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x12549d 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1254a1 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1254a1) (cmpR32Imm8Effect 0x1254a1 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1254a1 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1254a1 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1254a4 5 0x95) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12549d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12549d :=
  Rest.liftedBlock (rest_l12549d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12549d x hx)

theorem rest_l1254aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1254aa bytes_l1254aa) (entryMap (live .l1254aa))
      3 0x1254aa bytes_l1254aa b_l1254aa := by
  have f0 : InstrSpec 0x1254aa [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x1254aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1254aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1254aa 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1254aa 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1254aa 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1254af [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x1254af) (cmpR64Imm8Effect 0x1254af 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1254af 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x1254af 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254af) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1254b3 5 0x288) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1254aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1254aa :=
  Rest.liftedBlock (rest_l1254aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1254aa x hx)

theorem rest_l1254b9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1254b9 bytes_l1254b9) (entryMap (live .l1254b9))
      5 0x1254b9 bytes_l1254b9 b_l1254b9 := by
  have f0 : InstrSpec 0x1254b9 [0x4C, 0x89, 0x7C, 0x24, 0x70] (StorePre 0x1254b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1254b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1254b9 15 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1254b9 15 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1254b9 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1254be [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1254be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1254be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1254be 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1254be 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1254be 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1254c3 [0x44, 0x0F, 0xBE, 0x38] (LoadPre 0x1254c3 (fun s => AddrMode.addr (.base 0 .none) s (0x1254c3 + BitVec.ofNat 64 4)) 1) (movsxR32M8Effect 0x1254c3 4 15 (.base 0 .none))
      [.gpr 0] [] [.reg 15, .rip] :=
    (movsxR32M8Effect_footprint 0x1254c3 4 15 (.base 0 .none)).toInstrSpec (movsx_r32_m8_rex_effect_step 0x1254c3 0x44 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1254c7 [0x45, 0x85, 0xFF] (fun s => s.RIP = 0x1254c7) (testR32R32Effect 0x1254c7 3 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x1254c7 3 15 15).toInstrSpec (test_r32_r32_rex_effect_step 0x1254c7 0x45 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254be) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254c3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254c7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (20, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254ca) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x1254ca 8 0x109) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1254b9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1254b9 :=
  Rest.liftedBlock (rest_l1254b9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1254b9 x hx)

theorem rest_l1254d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1254d0 bytes_l1254d0) (entryMap (live .l1254d0))
      1 0x1254d0 bytes_l1254d0 b_l1254d0 := by
  have f0 : InstrSpec 0x1254d0 [0x45, 0x89, 0xFD] (fun s => s.RIP = 0x1254d0) (movR32R32Effect 0x1254d0 3 13 15)
      [.gpr 15] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x1254d0 3 13 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1254d0 0x45 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1254d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1254d0 :=
  Rest.liftedBlock (rest_l1254d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1254d0 x hx)

theorem rest_l1254d3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1254d3 bytes_l1254d3) (entryMap (live .l1254d3))
      7 0x1254d3 bytes_l1254d3 b_l1254d3 := by
  have f0 : InstrSpec 0x1254d3 [0x40, 0x80, 0xE5, 0x01] (fun s => s.RIP = 0x1254d3) (andR8Imm8Effect 0x1254d3 4 5 0x1)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x1254d3 4 5 0x1).toInstrSpec (and_r8_imm8_rex_effect_step 0x1254d3 0x40 0xe5 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1254d7 [0x48, 0x8B, 0x44, 0x24, 0x70] (LoadPre 0x1254d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1254d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1254d7 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1254d7 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x1254d7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1254dc [0x48, 0x89, 0x43, 0x04] (StorePre 0x1254dc 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1254dc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1254dc 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1254dc 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x1254dc 0x48 (by decide) 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1254e0 [0x44, 0x89, 0x6B, 0x0C] (StorePre 0x1254e0 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1254e0 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1254e0 13 (.base 3 (.d8 0xc)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x1254e0 13 (.base 3 (.d8 0xc))).toInstrSpec (mov_m32_r32_effect_step 0x1254e0 0x44 (by decide) 5 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1254e4 [0x40, 0x88, 0x6B, 0x10] (StorePre 0x1254e4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1254e4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1254e4 4 5 (.base 3 (.d8 0x10)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x1254e4 4 5 (.base 3 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1254e4 0x40 (by decide) 5 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1254e8 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x1254e8 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1254e8 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1254e8 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1254e8 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x1254e8 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254d7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254dc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254e0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254e4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254e8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254ee) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 61) (jmp_rel32_effect_step 0x1254ee 0xd4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1254d3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1254d3 :=
  Rest.liftedBlock (rest_l1254d3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1254d3 x hx)

theorem rest_l1254f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1254f3 bytes_l1254f3) (entryMap (live .l1254f3))
      18 0x1254f3 bytes_l1254f3 b_l1254f3 := by
  have f0 : InstrSpec 0x1254f3 [0x48, 0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x1254f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1254f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1254f3 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1254f3 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x1254f3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1254f8 [0x0F, 0xB6, 0x54, 0x24, 0x14] (LoadPre 0x1254f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1254f8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1254f8 5 2 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1254f8 5 2 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m8_effect_step 0x1254f8 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1254fd [0x8B, 0x74, 0x24, 0x3C] (LoadPre 0x1254fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1254fd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1254fd 6 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x1254fd 6 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x1254fd 6 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125501 [0x89, 0x73, 0x34] (StorePre 0x125501 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x125501 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125501 6 (.base 3 (.d8 0x34)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125501 6 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x125501 6 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125504 [0x48, 0x8B, 0x74, 0x24, 0x35] (LoadPre 0x125504 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x125504 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125504 6 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125504 6 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (mov_r64_m64_effect_step 0x125504 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125509 [0x48, 0x89, 0x73, 0x2D] (StorePre 0x125509 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2d)) s (0x125509 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125509 6 (.base 3 (.d8 0x2d)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125509 6 (.base 3 (.d8 0x2d))).toInstrSpec (mov_m64_r64_effect_step 0x125509 0x48 (by decide) 6 (.base 3 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x12550d [0x48, 0x8B, 0x74, 0x24, 0x2D] (LoadPre 0x12550d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x12550d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12550d 6 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12550d 6 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (mov_r64_m64_effect_step 0x12550d 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x125512 [0x48, 0x89, 0x73, 0x25] (StorePre 0x125512 4 (fun s => AddrMode.addr (.base 3 (.d8 0x25)) s (0x125512 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125512 6 (.base 3 (.d8 0x25)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125512 6 (.base 3 (.d8 0x25))).toInstrSpec (mov_m64_r64_effect_step 0x125512 0x48 (by decide) 6 (.base 3 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x125516 [0x48, 0x8B, 0x74, 0x24, 0x25] (LoadPre 0x125516 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x125516 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125516 6 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125516 6 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (mov_r64_m64_effect_step 0x125516 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x12551b [0x48, 0x89, 0x73, 0x1D] (StorePre 0x12551b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1d)) s (0x12551b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12551b 6 (.base 3 (.d8 0x1d)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12551b 6 (.base 3 (.d8 0x1d))).toInstrSpec (mov_m64_r64_effect_step 0x12551b 0x48 (by decide) 6 (.base 3 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x12551f [0x48, 0x8B, 0x74, 0x24, 0x1D] (LoadPre 0x12551f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x12551f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12551f 6 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12551f 6 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_r64_m64_effect_step 0x12551f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x125524 [0x48, 0x89, 0x73, 0x15] (StorePre 0x125524 4 (fun s => AddrMode.addr (.base 3 (.d8 0x15)) s (0x125524 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125524 6 (.base 3 (.d8 0x15)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125524 6 (.base 3 (.d8 0x15))).toInstrSpec (mov_m64_r64_effect_step 0x125524 0x48 (by decide) 6 (.base 3 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x125528 [0x48, 0x8B, 0x74, 0x24, 0x15] (LoadPre 0x125528 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x125528 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125528 6 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125528 6 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_r64_m64_effect_step 0x125528 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x12552d [0x48, 0x89, 0x73, 0x0D] (StorePre 0x12552d 4 (fun s => AddrMode.addr (.base 3 (.d8 0xd)) s (0x12552d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12552d 6 (.base 3 (.d8 0xd)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12552d 6 (.base 3 (.d8 0xd))).toInstrSpec (mov_m64_r64_effect_step 0x12552d 0x48 (by decide) 6 (.base 3 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125531 [0x89, 0x03] (StorePre 0x125531 2 (fun s => AddrMode.addr (.base 3 .none) s (0x125531 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x125531 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125531 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x125531 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x125533 [0x48, 0x89, 0x4B, 0x04] (StorePre 0x125533 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x125533 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125533 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125533 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x125533 0x48 (by decide) 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x125537 [0x88, 0x53, 0x0C] (StorePre 0x125537 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x125537 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x125537 3 2 (.base 3 (.d8 0xc)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x125537 3 2 (.base 3 (.d8 0xc))).toInstrSpec (mov_m8_r8_effect_step 0x125537 2 (by decide) (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1254fd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125501) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125504) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 60), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125509) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 60), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12550d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125512) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125516) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12551b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12551f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125524) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125528) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 72), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12552d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 72), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125531) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 72), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125533) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 72), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125537) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 72), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12553a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 78) (jmp_rel32_effect_step 0x12553a 0x88 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1254f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1254f3 :=
  Rest.liftedBlock (rest_l1254f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1254f3 x hx)

theorem rest_l12553f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12553f bytes_l12553f) (entryMap (live .l12553f))
      11 0x12553f bytes_l12553f b_l12553f := by
  have f0 : InstrSpec 0x12553f [0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x12553f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x12553f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12553f 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x12553f 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x12553f 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125543 [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x125543 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125543 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125543 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125543 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x125543 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125548 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x125548 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125548 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125548 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125548 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x125548 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12554d [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x12554d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12554d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12554d 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12554d 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x12554d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x125552 [0x48, 0x89, 0x7C, 0x24, 0x50] (StorePre 0x125552 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x125552 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125552 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125552 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x125552 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x125557 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x125557 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x125557 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125557 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125557 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x125557 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12555c [0x48, 0x89, 0x7C, 0x24, 0x58] (StorePre 0x12555c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12555c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12555c 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12555c 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x12555c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x125561 [0x48, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x125561 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x125561 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125561 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125561 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x125561 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125566 [0x48, 0x89, 0x7C, 0x24, 0x60] (StorePre 0x125566 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125566 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125566 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125566 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x125566 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12556b [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x12556b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12556b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12556b 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12556b 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x12556b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x125570 [0x48, 0x89, 0x7C, 0x24, 0x68] (StorePre 0x125570 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x125570 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125570 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125570 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x125570 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125543) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125548) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12554d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125552) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125557) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12555c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125561) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125566) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12556b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125570) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125575) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l12553f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12553f :=
  Rest.liftedBlock (rest_l12553f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12553f x hx)

theorem rest_l125575 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125575 bytes_l125575) (entryMap (live .l125575))
      2 0x125575 bytes_l125575 b_l125575 := by
  have f0 : InstrSpec 0x125575 [0x80, 0xFA, 0x0D] (fun s => s.RIP = 0x125575) (cmpR8Imm8Effect 0x125575 3 2 0xd)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x125575 3 2 0xd).toInstrSpec (cmp_r8_imm8_effect_step 0x125575 0xfa 0xd (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125578) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x125578 5 0x1c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125575 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125575 :=
  Rest.liftedBlock (rest_l125575 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125575 x hx)

theorem rest_l12557a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12557a bytes_l12557a) (entryMap (live .l12557a))
      7 0x12557a bytes_l12557a b_l12557a := by
  have f0 : InstrSpec 0x12557a [0x49, 0xC1, 0xE4, 0x20] (fun s => s.RIP = 0x12557a) (shlR64Effect 0x12557a 4 12 32)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR64Effect_footprint 0x12557a 4 12 32).toInstrSpec (shl_r64_imm8_effect_step 0x12557a 0x49 0xe4 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12557e [0x49, 0x83, 0xCC, 0x05] (fun s => s.RIP = 0x12557e) (orR64Imm8Effect 0x12557e 12 0x5)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x12557e 12 0x5).toInstrSpec (or_r64_imm8_effect_step 0x12557e 0x49 0xcc 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x125582 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x125582 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x125582 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x125582 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x125582 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x125582 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x125587 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x125587 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125587 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125587 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x125587 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x125587 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12558b [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12558b) (movR32Imm32Effect 0x12558b 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x12558b 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12558b 0xb8 (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x125590 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x125590) (movR64R64Effect 0x125590 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x125590 6 13).toInstrSpec (mov_r64_r64_effect_step 0x125590 0x4c 0xee (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x125593 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x125593) (movR64R64Effect 0x125593 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x125593 2 12).toInstrSpec (mov_r64_r64_effect_step 0x125593 0x4c 0xe2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12557e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125582) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125587) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 58), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12558b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 58), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125590) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 58), (3, 3), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125593) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 58), (2, 64), (3, 3), (4, 4), (6, 62), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125596) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l12557a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12557a :=
  Rest.liftedBlock (rest_l12557a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12557a x hx)

theorem rest_l125596 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125596 bytes_l125596) (entryMap (live .l125596))
      12 0x125596 bytes_l125596 b_l125596 := by
  have f0 : InstrSpec 0x125596 [0x89, 0x03] (StorePre 0x125596 2 (fun s => AddrMode.addr (.base 3 .none) s (0x125596 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x125596 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125596 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x125596 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x125598 [0x89, 0x4B, 0x04] (StorePre 0x125598 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x125598 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125598 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125598 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x125598 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12559b [0x48, 0x89, 0x53, 0x08] (StorePre 0x12559b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12559b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12559b 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12559b 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12559b 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x12559f [0x48, 0x89, 0x73, 0x10] (StorePre 0x12559f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12559f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12559f 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12559f 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12559f 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1255a3 [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x1255a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1255a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1255a3 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1255a3 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1255a3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1255a8 [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x1255a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1255a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1255a8 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1255a8 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1255a8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1255ad [0x48, 0x89, 0x43, 0x18] (StorePre 0x1255ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1255ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1255ad 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1255ad 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1255ad 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1255b1 [0x48, 0x89, 0x4B, 0x20] (StorePre 0x1255b1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1255b1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1255b1 1 (.base 3 (.d8 0x20)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1255b1 1 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1255b1 0x48 (by decide) 1 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1255b5 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x1255b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1255b5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1255b5 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1255b5 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x1255b5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1255ba [0x48, 0x89, 0x43, 0x28] (StorePre 0x1255ba 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1255ba + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1255ba 0 (.base 3 (.d8 0x28)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1255ba 0 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1255ba 0x48 (by decide) 0 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1255be [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x1255be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1255be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1255be 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1255be 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1255be 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1255c3 [0x48, 0x89, 0x43, 0x30] (StorePre 0x1255c3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1255c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1255c3 0 (.base 3 (.d8 0x30)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1255c3 0 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1255c3 0x48 (by decide) 0 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125598) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12559b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12559f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255a3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255a8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255ad) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255b1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255b5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255ba) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255be) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255c3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255c7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 69) (by decide) rfl

theorem block_l125596 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125596 :=
  Rest.liftedBlock (rest_l125596 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125596 x hx)

theorem rest_l1255c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1255c7 bytes_l1255c7) (entryMap (live .l1255c7))
      9 0x1255c7 bytes_l1255c7 b_l1255c7 := by
  have f0 : InstrSpec 0x1255c7 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1255c7) (movR64R64Effect 0x1255c7 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1255c7 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1255c7 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1255ca [0x48, 0x83, 0xC4, 0x78] (fun s => s.RIP = 0x1255ca) (addR64Imm8Effect 0x1255ca 4 0x78)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1255ca 4 0x78).toInstrSpec (add_r64_imm8_effect_step 0x1255ca 0x48 0xc4 0x78 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1255ce [0x5B] (PopPre 0x1255ce) (popR64Effect 0x1255ce 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1255ce 1 3).toInstrSpec (pop_r64_effect_step 0x1255ce 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1255cf [0x41, 0x5C] (PopPre 0x1255cf) (popR64Effect 0x1255cf 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1255cf 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1255cf 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1255d1 [0x41, 0x5D] (PopPre 0x1255d1) (popR64Effect 0x1255d1 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1255d1 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1255d1 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1255d3 [0x41, 0x5E] (PopPre 0x1255d3) (popR64Effect 0x1255d3 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1255d3 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1255d3 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1255d5 [0x41, 0x5F] (PopPre 0x1255d5) (popR64Effect 0x1255d5 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1255d5 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1255d5 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1255d7 [0x5D] (PopPre 0x1255d7) (popR64Effect 0x1255d7 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1255d7 1 5).toInstrSpec (pop_r64_effect_step 0x1255d7 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1255d8 [0xC3] (RetPre 0x1255d8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1255d8).toInstrSpec (ret_effect_step 0x1255d8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255ca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255ce) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255d1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255d3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255d5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255d7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255d8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l1255c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1255c7 :=
  Rest.liftedBlock (rest_l1255c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1255c7 x hx)

theorem rest_l1255d9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1255d9 bytes_l1255d9) (entryMap (live .l1255d9))
      3 0x1255d9 bytes_l1255d9 b_l1255d9 := by
  have f0 : InstrSpec 0x1255d9 [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x1255d9) (movR32R32Effect 0x1255d9 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1255d9 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1255d9 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1255dc [0xF6, 0xD8] (fun s => s.RIP = 0x1255dc) (negR8Effect 0x1255dc 2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR8Effect_footprint 0x1255dc 2 0).toInstrSpec (neg_r8_effect_step 0x1255dc 0xd8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255dc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .OF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (21, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255de) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x1255de 1 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1255d9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1255d9 :=
  Rest.liftedBlock (rest_l1255d9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1255d9 x hx)

theorem rest_l1255e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1255e0 bytes_l1255e0) (entryMap (live .l1255e0))
      5 0x1255e0 bytes_l1255e0 b_l1255e0 := by
  have f0 : InstrSpec 0x1255e0 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1255e0 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1255e0 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1255e0 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1255e0 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1255e0 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1255e5 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x1255e5 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1255e5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1255e5 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x1255e5 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1255e5 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1255e9 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1255e9) (movR32Imm32Effect 0x1255e9 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1255e9 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1255e9 0xb8 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x1255ee [0xBA, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1255ee) (movR32Imm32Effect 0x1255ee 5 2 0x4)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1255ee 5 2 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x1255ee 0xba (by decide) 0x4) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 54), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255e9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 54), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255f3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 60) (jmp_rel8_effect_step 0x1255f3 0x80 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1255e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1255e0 :=
  Rest.liftedBlock (rest_l1255e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1255e0 x hx)

theorem rest_l1255f5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1255f5 bytes_l1255f5) (entryMap (live .l1255f5))
      2 0x1255f5 bytes_l1255f5 b_l1255f5 := by
  have f0 : InstrSpec 0x1255f5 [0x41, 0x80, 0xFF, 0x85] (fun s => s.RIP = 0x1255f5) (cmpR8Imm8Effect 0x1255f5 4 15 0x85)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1255f5 4 15 0x85).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x1255f5 0x41 0xff 0x85 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1255f9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1255f9 3 0x83) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1255f5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1255f5 :=
  Rest.liftedBlock (rest_l1255f5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1255f5 x hx)

theorem rest_l1255ff [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1255ff bytes_l1255ff) (entryMap (live .l1255ff))
      3 0x1255ff bytes_l1255ff b_l1255ff := by
  have f0 : InstrSpec 0x1255ff [0x4C, 0x89, 0x6C, 0x24, 0x48] (StorePre 0x1255ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1255ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1255ff 13 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1255ff 13 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1255ff 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x125604 [0x41, 0xF6, 0xC7, 0x7F] (fun s => s.RIP = 0x125604) (testR8Imm8Effect 0x125604 15 0x7f)
      [.gpr 15] [] [.flags, .rip] :=
    (testR8Imm8Effect_footprint 0x125604 15 0x7f).toInstrSpec (test_r8_imm8_effect_step 0x125604 0x41 0xc7 0x7f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125604) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125608) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x125608 4 0x8c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1255ff [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1255ff :=
  Rest.liftedBlock (rest_l1255ff code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1255ff x hx)

theorem rest_l12560e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12560e bytes_l12560e) (entryMap (live .l12560e))
      5 0x12560e bytes_l12560e b_l12560e := by
  have f0 : InstrSpec 0x12560e [0x4C, 0x89, 0x64, 0x24, 0x40] (StorePre 0x12560e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12560e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12560e 12 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12560e 12 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x12560e 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x125613 [0x45, 0x89, 0xFC] (fun s => s.RIP = 0x125613) (movR32R32Effect 0x125613 3 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x125613 3 12 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x125613 0x45 0xfc (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x125616 [0x41, 0x83, 0xE4, 0x7F] (fun s => s.RIP = 0x125616) (andR32Imm8Effect 0x125616 4 12 0x7f)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x125616 4 12 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x125616 0x41 0xe4 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12561a [0x45, 0x31, 0xED] (fun s => s.RIP = 0x12561a) (xorR32R32Effect 0x12561a 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12561a 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x12561a 0x45 0xed (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12561d [0x0F, 0x1F, 0x00] (fun s => s.RIP = 0x12561d) (fun _ => nopEffect 0x12561d 3)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12561d 3).toInstrSpec (nop_m_effect_step 0x12561d [] (by decide) (by decide) (.base 0 .none) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125613) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 54), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125616) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12561a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12561d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125620) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l12560e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12560e :=
  Rest.liftedBlock (rest_l12560e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12560e x hx)

theorem rest_l125620 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125620 bytes_l125620) (entryMap (live .l125620))
      4 0x125620 bytes_l125620 b_l125620 := by
  have f0 : InstrSpec 0x125620 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x125620) (leaR64Effect 0x125620 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x125620 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x125620 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125625 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x125625) (movR64R64Effect 0x125625 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x125625 6 14).toInstrSpec (mov_r64_r64_effect_step 0x125625 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x125628 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125628) (movR32Imm32Effect 0x125628 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x125628 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x125628 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x12562d [0xE8, 0x4E, 0x25, 0x00, 0x00] (PushPre 0x12562d 5) (callEffect (fun _ => 0x127b80) 0x125632)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12562d 0x127b80 0x125632).toInstrSpec (call_rel32_effect_step 0x12562d 0x254e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125625) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125628) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12562d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l125620 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125620 :=
  Rest.liftedBlock (rest_l125620 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125620 x hx)

theorem rest_l125632 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125632 bytes_l125632) (entryMap (live .l125632))
      3 0x125632 bytes_l125632 b_l125632 := by
  have f0 : InstrSpec 0x125632 [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x125632 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125632 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125632 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x125632 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x125632 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125636 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x125636) (cmpR32Imm8Effect 0x125636 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x125636 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x125636 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125636) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125639) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x125639 5 0x9f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125632 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125632 :=
  Rest.liftedBlock (rest_l125632 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125632 x hx)

theorem rest_l12563f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12563f bytes_l12563f) (entryMap (live .l12563f))
      3 0x12563f bytes_l12563f b_l12563f := by
  have f0 : InstrSpec 0x12563f [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x12563f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12563f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12563f 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12563f 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12563f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125644 [0x48, 0x83, 0xFE, 0x01] (fun s => s.RIP = 0x125644) (cmpR64Imm8Effect 0x125644 6 0x1)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x125644 6 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x125644 0x48 0xfe 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125644) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125648) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x125648 5 0xf3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12563f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12563f :=
  Rest.liftedBlock (rest_l12563f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12563f x hx)

theorem rest_l12564e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12564e bytes_l12564e) (entryMap (live .l12564e))
      7 0x12564e bytes_l12564e b_l12564e := by
  have f0 : InstrSpec 0x12564e [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x12564e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12564e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12564e 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12564e 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12564e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125653 [0x44, 0x89, 0xEA] (fun s => s.RIP = 0x125653) (movR32R32Effect 0x125653 3 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x125653 3 2 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x125653 0x44 0xea (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x125656 [0x44, 0x0F, 0xB6, 0x28] (LoadPre 0x125656 (fun s => AddrMode.addr (.base 0 .none) s (0x125656 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x125656 4 13 (.base 0 .none))
      [.gpr 0] [] [.reg 13, .rip] :=
    (movzxR32M8Effect_footprint 0x125656 4 13 (.base 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125656 0x44 (by decide) 5 (.base 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12565a [0xC1, 0xE2, 0x08] (fun s => s.RIP = 0x12565a) (shlR32Effect 0x12565a 3 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x12565a 3 2 8).toInstrSpec (shl_r32_imm8_effect_step 0x12565a 0xe2 0x8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12565d [0x41, 0x09, 0xD5] (fun s => s.RIP = 0x12565d) (orR32R32Effect 0x12565d 3 13 2)
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (orR32R32Effect_footprint 0x12565d 3 13 2).toInstrSpec (or_r32_r32_rex_effect_step 0x12565d 0x41 0xd5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x125660 [0x49, 0xFF, 0xCC] (fun s => s.RIP = 0x125660) (decR64Effect 0x125660 12)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (decR64Effect_footprint 0x125660 12).toInstrSpec (dec_r64_effect_step 0x125660 0x49 0xcc (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125653) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125656) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12565a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12565d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125660) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 64) f5 .ZF (fun _ => rfl) (decR64Effect_fresh 0x125660 12 _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 63), (13, 61), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125663) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x125663 5 0xbb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12564e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12564e :=
  Rest.liftedBlock (rest_l12564e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12564e x hx)

theorem rest_l125665 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125665 bytes_l125665) (entryMap (live .l125665))
      6 0x125665 bytes_l125665 b_l125665 := by
  have f0 : InstrSpec 0x125665 [0x44, 0x89, 0xEE] (fun s => s.RIP = 0x125665) (movR32R32Effect 0x125665 3 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x125665 3 6 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x125665 0x44 0xee (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125668 [0x83, 0xE6, 0x80] (fun s => s.RIP = 0x125668) (andR32Imm8Effect 0x125668 3 6 0x80)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x125668 3 6 0x80).toInstrSpec (and_r32_imm8_effect_step 0x125668 0xe6 0x80 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12566b [0xB0, 0x01] (fun s => s.RIP = 0x12566b) (movR8Imm8Effect 0x12566b 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x12566b 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x12566b 0xb0 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x12566d [0xB1, 0x81] (fun s => s.RIP = 0x12566d) (movR8Imm8Effect 0x12566d 2 1 0x81)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x12566d 2 1 0x81).toInstrSpec (mov_r8_imm8_effect_step 0x12566d 0xb1 (by decide) 0x81) pre_rip
  have f4 : InstrSpec 0x12566f [0x81, 0xFE, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12566f) (cmpR32Imm32Effect 0x12566f 6 6 0x80)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR32Imm32Effect_footprint 0x12566f 6 6 0x80).toInstrSpec (cmp_r32_imm32_effect_step 0x12566f 0xfe 0x80 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125668) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12566b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12566d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12566f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125675) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel32_effect_step 0x125675 5 0xa8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125665 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125665 :=
  Rest.liftedBlock (rest_l125665 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125665 x hx)

theorem rest_l12567b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12567b bytes_l12567b) (entryMap (live .l12567b))
      2 0x12567b bytes_l12567b b_l12567b := by
  have f0 : InstrSpec 0x12567b [0x4C, 0x8B, 0x64, 0x24, 0x40] (LoadPre 0x12567b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12567b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12567b 12 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x12567b 12 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x12567b 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125680) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x125680 0x32 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12567b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12567b :=
  Rest.liftedBlock (rest_l12567b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12567b x hx)

theorem rest_l125682 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125682 bytes_l125682) (entryMap (live .l125682))
      5 0x125682 bytes_l125682 b_l125682 := by
  have f0 : InstrSpec 0x125682 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x125682 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x125682 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x125682 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x125682 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x125682 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x125687 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x125687 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x125687 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x125687 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x125687 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x125687 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12568b [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12568b) (movR32Imm32Effect 0x12568b 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x12568b 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12568b 0xb8 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x125690 [0xBA, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125690) (movR32Imm32Effect 0x125690 5 2 0xd)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x125690 5 2 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x125690 0xba (by decide) 0xd) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125687) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 54), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12568b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 54), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125690) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125695) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 60) (jmp_rel32_effect_step 0x125695 0xfffffedb (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125682 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125682 :=
  Rest.liftedBlock (rest_l125682 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125682 x hx)

theorem rest_l12569a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12569a bytes_l12569a) (entryMap (live .l12569a))
      1 0x12569a bytes_l12569a b_l12569a := by
  have f0 : InstrSpec 0x12569a [0x45, 0x31, 0xED] (fun s => s.RIP = 0x12569a) (xorR32R32Effect 0x12569a 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12569a 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x12569a 0x45 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12569d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l12569a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12569a :=
  Rest.liftedBlock (rest_l12569a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12569a x hx)

theorem rest_l12569d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12569d bytes_l12569d) (entryMap (live .l12569d))
      6 0x12569d bytes_l12569d b_l12569d := by
  have f0 : InstrSpec 0x12569d [0x44, 0x89, 0xE9] (fun s => s.RIP = 0x12569d) (movR32R32Effect 0x12569d 3 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12569d 3 1 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x12569d 0x44 0xe9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1256a0 [0x81, 0xE9, 0x00, 0x00, 0x01, 0x00] (fun s => s.RIP = 0x1256a0) (subR32Imm32Effect 0x1256a0 6 1 0x10000)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (subR32Imm32Effect_footprint 0x1256a0 6 1 0x10000).toInstrSpec (sub_r32_imm32_effect_step 0x1256a0 0xe9 0x10000 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1256a6 [0x0F, 0x93, 0xC0] (fun s => s.RIP = 0x1256a6) (atFlags (condHolds 3) (setccR8Effect 0x1256a6 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1256a6 3 0 3).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1256a6 3 0xc0 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x1256a9 [0x81, 0xF9, 0x00, 0x00, 0xFF, 0x00] (fun s => s.RIP = 0x1256a9) (cmpR32Imm32Effect 0x1256a9 6 1 0xff0000)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm32Effect_footprint 0x1256a9 6 1 0xff0000).toInstrSpec (cmp_r32_imm32_effect_step 0x1256a9 0xf9 0xff0000 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1256af [0xB1, 0x84] (fun s => s.RIP = 0x1256af) (movR8Imm8Effect 0x1256af 2 1 0x84)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x1256af 2 1 0x84).toInstrSpec (mov_r8_imm8_effect_step 0x1256af 0xb1 (by decide) 0x84) pre_rip
  have f5 : InstrSpec 0x1256b1 [0x80, 0xD9, 0x00] (fun s => s.RIP = 0x1256b1) (atFlags StatusFlags.CF (sbbR8Imm8Effect 0x1256b1 3 1 0x0))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (sbbR8Imm8Effect_footprint 0x1256b1 3 1 0x0).toInstrSpec (StepEffect.atFlags fun c => (sbb_r8_imm8_effect_step 0x1256b1 0xd9 0x0 c (by decide) (by decide) (by decide))) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256a6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256a9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256af) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 58), (1, 62), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256b1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 58), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256b4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l12569d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12569d :=
  Rest.liftedBlock (rest_l12569d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12569d x hx)

theorem rest_l1256b4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1256b4 bytes_l1256b4) (entryMap (live .l1256b4))
      2 0x1256b4 bytes_l1256b4 b_l1256b4 := by
  have f0 : InstrSpec 0x1256b4 [0x84, 0xC0] (fun s => s.RIP = 0x1256b4) (testR8R8Effect 0x1256b4 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1256b4 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x1256b4 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256b6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1256b6 4 0x9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1256b4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1256b4 :=
  Rest.liftedBlock (rest_l1256b4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1256b4 x hx)

theorem rest_l1256b8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1256b8 bytes_l1256b8) (entryMap (live .l1256b8))
      2 0x1256b8 bytes_l1256b8 b_l1256b8 := by
  have f0 : InstrSpec 0x1256b8 [0x44, 0x38, 0xF9] (fun s => s.RIP = 0x1256b8) (cmpR8R8Effect 0x1256b8 3 1 15)
      [.gpr 1, .gpr 15] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x1256b8 3 1 15).toInstrSpec (cmp_r8_r8_rex_effect_step 0x1256b8 0x44 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256bb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1256bb 4 0xfffffe12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1256b8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1256b8 :=
  Rest.liftedBlock (rest_l1256b8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1256b8 x hx)

theorem rest_l1256c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1256c1 bytes_l1256c1) (entryMap (live .l1256c1))
      6 0x1256c1 bytes_l1256c1 b_l1256c1 := by
  have f0 : InstrSpec 0x1256c1 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1256c1 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1256c1 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1256c1 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1256c1 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1256c1 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1256c6 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x1256c6 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1256c6 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1256c6 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x1256c6 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1256c6 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1256ca [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1256ca) (movR32Imm32Effect 0x1256ca 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1256ca 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1256ca 0xb8 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x1256cf [0xBA, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1256cf) (movR32Imm32Effect 0x1256cf 5 2 0xd)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1256cf 5 2 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x1256cf 0xba (by decide) 0xd) pre_rip
  have f4 : InstrSpec 0x1256d4 [0x4C, 0x8B, 0x6C, 0x24, 0x48] (LoadPre 0x1256d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1256d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256d4 13 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1256d4 13 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x1256d4 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256c6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 54), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 54), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256d4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 60), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256d9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 62) (jmp_rel32_effect_step 0x1256d9 0xfffffe97 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1256c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1256c1 :=
  Rest.liftedBlock (rest_l1256c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1256c1 x hx)

theorem rest_l1256de [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1256de bytes_l1256de) (entryMap (live .l1256de))
      14 0x1256de bytes_l1256de b_l1256de := by
  have f0 : InstrSpec 0x1256de [0x8B, 0x4C, 0x24, 0x0C] (LoadPre 0x1256de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1256de + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1256de 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1256de 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x1256de 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1256e2 [0x48, 0x8B, 0x54, 0x24, 0x10] (LoadPre 0x1256e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1256e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256e2 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1256e2 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1256e2 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1256e7 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x1256e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1256e7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256e7 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1256e7 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1256e7 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1256ec [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x1256ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1256ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256ec 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1256ec 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1256ec 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1256f1 [0x48, 0x89, 0x7C, 0x24, 0x50] (StorePre 0x1256f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1256f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1256f1 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1256f1 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x1256f1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1256f6 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x1256f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1256f6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1256f6 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1256f6 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1256f6 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1256fb [0x48, 0x89, 0x7C, 0x24, 0x58] (StorePre 0x1256fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1256fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1256fb 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1256fb 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1256fb 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x125700 [0x48, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x125700 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x125700 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125700 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125700 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x125700 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125705 [0x48, 0x89, 0x7C, 0x24, 0x60] (StorePre 0x125705 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125705 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125705 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125705 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x125705 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12570a [0x48, 0x8B, 0x7C, 0x24, 0x38] (LoadPre 0x12570a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12570a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12570a 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12570a 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x12570a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x12570f [0x48, 0x89, 0x7C, 0x24, 0x68] (StorePre 0x12570f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12570f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12570f 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12570f 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x12570f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x125714 [0x4C, 0x8B, 0x64, 0x24, 0x40] (LoadPre 0x125714 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125714 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125714 12 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x125714 12 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x125714 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x125719 [0x4C, 0x8B, 0x6C, 0x24, 0x48] (LoadPre 0x125719 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x125719 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125719 13 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x125719 13 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x125719 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256e2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256e7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256ec) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256f1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256f6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1256fb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125700) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125705) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12570a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12570f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125714) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125719) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (6, 57), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 71), (13, 73), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12571e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 75) (jmp_rel32_effect_step 0x12571e 0xfffffe52 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1256de [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1256de :=
  Rest.liftedBlock (rest_l1256de code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1256de x hx)

theorem rest_l125723 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125723 bytes_l125723) (entryMap (live .l125723))
      5 0x125723 bytes_l125723 b_l125723 := by
  have f0 : InstrSpec 0x125723 [0x81, 0xC2, 0x00, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x125723) (addR32Imm32Effect 0x125723 6 2 0xffffff00)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR32Imm32Effect_footprint 0x125723 6 2 0xffffff00).toInstrSpec (add_r32_imm32_effect_step 0x125723 0xc2 0xffffff00 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125729 [0xB1, 0x82] (fun s => s.RIP = 0x125729) (movR8Imm8Effect 0x125729 2 1 0x82)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x125729 2 1 0x82).toInstrSpec (mov_r8_imm8_effect_step 0x125729 0xb1 (by decide) 0x82) pre_rip
  have f2 : InstrSpec 0x12572b [0x81, 0xFA, 0x00, 0xFF, 0x00, 0x00] (fun s => s.RIP = 0x12572b) (cmpR32Imm32Effect 0x12572b 6 2 0xff00)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm32Effect_footprint 0x12572b 6 2 0xff00).toInstrSpec (cmp_r32_imm32_effect_step 0x12572b 0xfa 0xff00 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x125731 [0x4C, 0x8B, 0x64, 0x24, 0x40] (LoadPre 0x125731 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125731 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125731 12 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x125731 12 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x125731 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125729) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12572b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125731) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125736) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x125736 3 0xffffff61) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125723 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125723 :=
  Rest.liftedBlock (rest_l125723 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125723 x hx)

theorem rest_l12573c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12573c bytes_l12573c) (entryMap (live .l12573c))
      1 0x12573c bytes_l12573c b_l12573c := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x12573c 0xffffff73 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12573c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12573c :=
  Rest.liftedBlock (rest_l12573c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12573c x hx)

theorem rest_l125741 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125741 bytes_l125741) (entryMap (live .l125741))
      3 0x125741 bytes_l125741 b_l125741 := by
  have f0 : InstrSpec 0x125741 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125741) (movR32Imm32Effect 0x125741 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x125741 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x125741 0xbf (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x125746 [0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x125746) (movR64Imm32Effect 0x125746 2 0x2036e0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x125746 2 0x2036e0).toInstrSpec (mov_r64_imm32_effect_step 0x125746 0x48 0xc2 (by decide) (by decide) (by decide) 0x2036e0) pre_rip
  have f2 : InstrSpec 0x12574d [0xE8, 0x3E, 0x45, 0x00, 0x00] (PushPre 0x12574d 5) (callEffect (fun _ => 0x129c90) 0x125752)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12574d 0x129c90 0x125752).toInstrSpec (call_rel32_effect_step 0x12574d 0x453e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x125746) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x12574d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l125741 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125741 :=
  Rest.liftedBlock (rest_l125741 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125741 x hx)

theorem rest_l125752 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125752 bytes_l125752) (entryMap (live .l125752))
      2 0x125752 bytes_l125752 b_l125752 := by
  have f0 : InstrSpec 0x125752 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125752) (fun _ => nopEffect 0x125752 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x125752 10).toInstrSpec (nop_m_effect_step 0x125752 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12575c [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x12575c) (fun _ => nopEffect 0x12575c 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12575c 4).toInstrSpec (nop_m_effect_step 0x12575c [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12575c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125760) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l125752 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125752 :=
  Rest.liftedBlock (rest_l125752 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125752 x hx)

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

theorem_by block_l125450_eval :
    program.runBlock (dialect code) ⟨.l125450, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12546e_eval :
    program.runBlock (dialect code) ⟨.l12546e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125477_eval :
    program.runBlock (dialect code) ⟨.l125477, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12549d_eval :
    program.runBlock (dialect code) ⟨.l12549d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1254aa_eval :
    program.runBlock (dialect code) ⟨.l1254aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1254b9_eval :
    program.runBlock (dialect code) ⟨.l1254b9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1254d0_eval :
    program.runBlock (dialect code) ⟨.l1254d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1254d3_eval :
    program.runBlock (dialect code) ⟨.l1254d3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1254f3_eval :
    program.runBlock (dialect code) ⟨.l1254f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12553f_eval :
    program.runBlock (dialect code) ⟨.l12553f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125575_eval :
    program.runBlock (dialect code) ⟨.l125575, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12557a_eval :
    program.runBlock (dialect code) ⟨.l12557a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125596_eval :
    program.runBlock (dialect code) ⟨.l125596, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1255c7_eval :
    program.runBlock (dialect code) ⟨.l1255c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1255d9_eval :
    program.runBlock (dialect code) ⟨.l1255d9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1255e0_eval :
    program.runBlock (dialect code) ⟨.l1255e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1255f5_eval :
    program.runBlock (dialect code) ⟨.l1255f5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1255ff_eval :
    program.runBlock (dialect code) ⟨.l1255ff, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12560e_eval :
    program.runBlock (dialect code) ⟨.l12560e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125620_eval :
    program.runBlock (dialect code) ⟨.l125620, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125632_eval :
    program.runBlock (dialect code) ⟨.l125632, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12563f_eval :
    program.runBlock (dialect code) ⟨.l12563f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12564e_eval :
    program.runBlock (dialect code) ⟨.l12564e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125665_eval :
    program.runBlock (dialect code) ⟨.l125665, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12567b_eval :
    program.runBlock (dialect code) ⟨.l12567b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125682_eval :
    program.runBlock (dialect code) ⟨.l125682, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12569a_eval :
    program.runBlock (dialect code) ⟨.l12569a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12569d_eval :
    program.runBlock (dialect code) ⟨.l12569d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1256b4_eval :
    program.runBlock (dialect code) ⟨.l1256b4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1256b8_eval :
    program.runBlock (dialect code) ⟨.l1256b8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1256c1_eval :
    program.runBlock (dialect code) ⟨.l1256c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1256de_eval :
    program.runBlock (dialect code) ⟨.l1256de, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125723_eval :
    program.runBlock (dialect code) ⟨.l125723, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12573c_eval :
    program.runBlock (dialect code) ⟨.l12573c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125741_eval :
    program.runBlock (dialect code) ⟨.l125741, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125752_eval :
    program.runBlock (dialect code) ⟨.l125752, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
