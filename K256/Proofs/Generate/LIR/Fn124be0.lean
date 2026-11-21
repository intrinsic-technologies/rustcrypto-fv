import K256.Proofs.Generate.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Generate.LIR.Generated.Values

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

theorem rest_l124be0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124be0 bytes_l124be0) (entryMap (live .l124be0))
      9 0x124be0 bytes_l124be0 b_l124be0 := by
  have f0 : InstrSpec 0x124be0 [0x55] (PushPre 0x124be0 1) (pushR64Effect 0x124be0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124be0 1 5).toInstrSpec (push_r64_effect_step 0x124be0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x124be1 [0x41, 0x57] (PushPre 0x124be1 2) (pushR64Effect 0x124be1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124be1 2 15).toInstrSpec (push_r64_rex_effect_step 0x124be1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124be3 [0x41, 0x56] (PushPre 0x124be3 2) (pushR64Effect 0x124be3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124be3 2 14).toInstrSpec (push_r64_rex_effect_step 0x124be3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124be5 [0x53] (PushPre 0x124be5 1) (pushR64Effect 0x124be5 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124be5 1 3).toInstrSpec (push_r64_effect_step 0x124be5 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124be6 [0x48, 0x83, 0xEC, 0x48] (fun s => s.RIP = 0x124be6) (subR64Imm8Effect 0x124be6 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x124be6 4 0x48).toInstrSpec (sub_r64_imm8_effect_step 0x124be6 0x48 0xec 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x124bea [0x66, 0xC7, 0x44, 0x24, 0x0C, 0x00, 0x00] (StorePre 0x124bea 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124bea + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x124bea (.sib 4 none 0 (.d8 0xc)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x124bea (.sib 4 none 0 (.d8 0xc)) 0x0).toInstrSpec (mov_m16_imm16_effect_step 0x124bea (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124bf1 [0x8B, 0x5A, 0x08] (LoadPre 0x124bf1 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x124bf1 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124bf1 3 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x124bf1 3 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x124bf1 3 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124bf4 [0x48, 0x85, 0xDB] (fun s => s.RIP = 0x124bf4) (testR64R64Effect 0x124bf4 3 3)
      [.gpr 3, .gpr 3] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x124bf4 3 3).toInstrSpec (test_r64_r64_effect_step 0x124bf4 0x48 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124be1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124be3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124be5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124be6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bea) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bf1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 1), (2, 2), (3, 64), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bf4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (3, 64), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bf7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x124bf7 4 0x26) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124be0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124be0 :=
  Rest.liftedBlock (rest_l124be0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124be0 x hx)

theorem rest_l124bf9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124bf9 bytes_l124bf9) (entryMap (live .l124bf9))
      2 0x124bf9 bytes_l124bf9 b_l124bf9 := by
  have f0 : InstrSpec 0x124bf9 [0x83, 0xFB, 0x02] (fun s => s.RIP = 0x124bf9) (cmpR32Imm8Effect 0x124bf9 3 3 0x2)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124bf9 3 3 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124bf9 0xfb 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bfc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x124bfc 6 0x3e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124bf9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124bf9 :=
  Rest.liftedBlock (rest_l124bf9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124bf9 x hx)

theorem rest_l124bfe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124bfe bytes_l124bfe) (entryMap (live .l124bfe))
      2 0x124bfe bytes_l124bfe b_l124bfe := by
  have f0 : InstrSpec 0x124bfe [0xC6, 0x46, 0x20, 0x01] (StorePre 0x124bfe 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x124bfe + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124bfe (.base 6 (.d8 0x20)) 0x1)
      [.gpr 6] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x124bfe (.base 6 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x124bfe (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124c02 [0x8B, 0x46, 0x1C] (LoadPre 0x124c02 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x124c02 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124c02 0 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124c02 0 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x124c02 0 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c02) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l124bfe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124bfe :=
  Rest.liftedBlock (rest_l124bfe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124bfe x hx)

theorem rest_l124c05 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c05 bytes_l124c05) (entryMap (live .l124c05))
      5 0x124c05 bytes_l124c05 b_l124c05 := by
  have f0 : InstrSpec 0x124c05 [0xC7, 0x07, 0x01, 0x00, 0x00, 0x00] (StorePre 0x124c05 6 (fun s => AddrMode.addr (.base 7 .none) s (0x124c05 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124c05 6 (.base 7 .none) 0x1)
      [.gpr 7] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124c05 6 (.base 7 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x124c05 (.base 7 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124c0b [0x89, 0x47, 0x04] (StorePre 0x124c0b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x124c0b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124c0b 0 (.base 7 (.d8 0x4)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124c0b 0 (.base 7 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x124c0b 0 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x124c0e [0xC6, 0x47, 0x08, 0x07] (StorePre 0x124c0e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x124c0e + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124c0e (.base 7 (.d8 0x8)) 0x7)
      [.gpr 7] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x124c0e (.base 7 (.d8 0x8)) 0x7).toInstrSpec (mov_m8_imm8_effect_step 0x124c0e (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide) 0x7) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124c12 [0x48, 0xC7, 0x47, 0x0C, 0x01, 0x00, 0x00, 0x00] (StorePre 0x124c12 8 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x124c12 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x124c12 (.base 7 (.d8 0xc)) 0x1)
      [.gpr 7] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124c12 (.base 7 (.d8 0xc)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x124c12 0x48 (by decide) (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c0b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c0e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c12) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c1a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x124c1a 0x194 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124c05 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c05 :=
  Rest.liftedBlock (rest_l124c05 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c05 x hx)

theorem rest_l124c1f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c1f bytes_l124c1f) (entryMap (live .l124c1f))
      7 0x124c1f bytes_l124c1f b_l124c1f := by
  have f0 : InstrSpec 0x124c1f [0xC6, 0x46, 0x20, 0x01] (StorePre 0x124c1f 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x124c1f + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124c1f (.base 6 (.d8 0x20)) 0x1)
      [.gpr 6] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x124c1f (.base 6 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x124c1f (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124c23 [0x8B, 0x46, 0x1C] (LoadPre 0x124c23 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x124c23 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124c23 0 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124c23 0 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x124c23 0 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124c26 [0xC7, 0x07, 0x01, 0x00, 0x00, 0x00] (StorePre 0x124c26 6 (fun s => AddrMode.addr (.base 7 .none) s (0x124c26 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124c26 6 (.base 7 .none) 0x1)
      [.gpr 7] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124c26 6 (.base 7 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x124c26 (.base 7 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124c2c [0x89, 0x47, 0x04] (StorePre 0x124c2c 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x124c2c + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124c2c 0 (.base 7 (.d8 0x4)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124c2c 0 (.base 7 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x124c2c 0 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124c2f [0xC6, 0x47, 0x08, 0x05] (StorePre 0x124c2f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x124c2f + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124c2f (.base 7 (.d8 0x8)) 0x5)
      [.gpr 7] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x124c2f (.base 7 (.d8 0x8)) 0x5).toInstrSpec (mov_m8_imm8_effect_step 0x124c2f (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide) 0x5) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124c33 [0xC6, 0x47, 0x0C, 0x01] (StorePre 0x124c33 4 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x124c33 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124c33 (.base 7 (.d8 0xc)) 0x1)
      [.gpr 7] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x124c33 (.base 7 (.d8 0xc)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x124c33 (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c23) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c26) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c2c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c2f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c33) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c37) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 60) (jmp_rel32_effect_step 0x124c37 0x177 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124c1f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c1f :=
  Rest.liftedBlock (rest_l124c1f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c1f x hx)

theorem rest_l124c3c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c3c bytes_l124c3c) (entryMap (live .l124c3c))
      5 0x124c3c bytes_l124c3c b_l124c3c := by
  have f0 : InstrSpec 0x124c3c [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x124c3c) (movR64R64Effect 0x124c3c 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x124c3c 14 7).toInstrSpec (mov_r64_r64_effect_step 0x124c3c 0x49 0xfe (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124c3f [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x124c3f) (leaR64Effect 0x124c3f 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124c3f 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x124c3f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124c44 [0x49, 0x89, 0xF7] (fun s => s.RIP = 0x124c44) (movR64R64Effect 0x124c44 15 6)
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x124c44 15 6).toInstrSpec (mov_r64_r64_effect_step 0x124c44 0x49 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124c47 [0x89, 0xDA] (fun s => s.RIP = 0x124c47) (movR32R32Effect 0x124c47 2 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x124c47 2 2 3).toInstrSpec (mov_r32_r32_effect_step 0x124c47 0xda (by decide)) pre_rip
  have f4 : InstrSpec 0x124c49 [0xE8, 0x32, 0x2F, 0x00, 0x00] (PushPre 0x124c49 5) (callEffect (fun _ => 0x127b80) 0x124c4e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124c49 0x127b80 0x124c4e).toInstrSpec (call_rel32_effect_step 0x124c49 0x2f32 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c3f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c44) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c47) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c49) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b80) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l124c3c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c3c :=
  Rest.liftedBlock (rest_l124c3c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c3c x hx)

theorem rest_l124c4e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c4e bytes_l124c4e) (entryMap (live .l124c4e))
      3 0x124c4e bytes_l124c4e b_l124c4e := by
  have f0 : InstrSpec 0x124c4e [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x124c4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124c4e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124c4e 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124c4e 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x124c4e 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124c52 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124c52) (cmpR32Imm8Effect 0x124c52 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124c52 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124c52 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c52) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c55) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x124c55 5 0x4a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124c4e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c4e :=
  Rest.liftedBlock (rest_l124c4e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c4e x hx)

theorem rest_l124c57 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c57 bytes_l124c57) (entryMap (live .l124c57))
      3 0x124c57 bytes_l124c57 b_l124c57 := by
  have f0 : InstrSpec 0x124c57 [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x124c57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124c57 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124c57 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124c57 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x124c57 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124c5c [0x48, 0x39, 0xDE] (fun s => s.RIP = 0x124c5c) (cmpR64R64Effect 0x124c5c 6 3)
      [.gpr 6, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x124c5c 6 3).toInstrSpec (cmp_r64_r64_effect_step 0x124c5c 0x48 0xde (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c5c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c5f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x124c5f 5 0x16a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124c57 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c57 :=
  Rest.liftedBlock (rest_l124c57 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c57 x hx)

theorem rest_l124c65 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c65 bytes_l124c65) (entryMap (live .l124c65))
      4 0x124c65 bytes_l124c65 b_l124c65 := by
  have f0 : InstrSpec 0x124c65 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x124c65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124c65 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124c65 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124c65 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x124c65 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124c6a [0x48, 0x8D, 0x7C, 0x24, 0x0C] (fun s => s.RIP = 0x124c6a) (leaR64Effect 0x124c6a 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124c6a 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (lea_r64_effect_step 0x124c6a 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124c6f [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x124c6f) (movR64R64Effect 0x124c6f 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x124c6f 2 3).toInstrSpec (mov_r64_r64_effect_step 0x124c6f 0x48 0xda (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124c72 [0xFF, 0x15, 0x58, 0xF1, 0x0D, 0x00] (GoesTo (CallMemPre 0x124c72 (.rip 0xdf158)) (callEffect (callMemPtr 0x124c72 (.rip 0xdf158)) (0x124c72 + BitVec.ofNat 64 (callMemLen (.rip 0xdf158)))) 0x12a820) (callEffect (callMemPtr 0x124c72 (.rip 0xdf158)) (0x124c72 + BitVec.ofNat 64 (callMemLen (.rip 0xdf158))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x124c72 (.rip 0xdf158)).toInstrSpec (call_m64_effect_step 0x124c72 (.rip 0xdf158) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c6a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c6f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c72) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l124c65 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c65 :=
  Rest.liftedBlock (rest_l124c65 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c65 x hx)

theorem rest_l124c78 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c78 bytes_l124c78) (entryMap (live .l124c78))
      3 0x124c78 bytes_l124c78 b_l124c78 := by
  have f0 : InstrSpec 0x124c78 [0x0F, 0xB6, 0x6C, 0x24, 0x0C] (LoadPre 0x124c78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x124c78 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x124c78 5 5 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x124c78 5 5 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x124c78 5 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124c7d [0x48, 0x83, 0xFB, 0x01] (fun s => s.RIP = 0x124c7d) (cmpR64Imm8Effect 0x124c7d 3 0x1)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x124c7d 3 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x124c7d 0x48 0xfb 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c7d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c81) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x124c81 5 0x67) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124c78 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c78 :=
  Rest.liftedBlock (rest_l124c78 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c78 x hx)

theorem rest_l124c83 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c83 bytes_l124c83) (entryMap (live .l124c83))
      2 0x124c83 bytes_l124c83 b_l124c83 := by
  have f0 : InstrSpec 0x124c83 [0x40, 0x84, 0xED] (fun s => s.RIP = 0x124c83) (testR8R8Effect 0x124c83 3 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x124c83 3 5 5).toInstrSpec (test_r8_r8_rex_effect_step 0x124c83 0x40 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (20, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c86) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x124c86 4 0x80) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124c83 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c83 :=
  Rest.liftedBlock (rest_l124c83 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c83 x hx)

theorem rest_l124c8c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c8c bytes_l124c8c) (entryMap (live .l124c8c))
      1 0x124c8c bytes_l124c8c b_l124c8c := by
  exact Rest.jcc (n := 53) (jcc_rel32_effect_step 0x124c8c 9 0xad) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124c8c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c8c :=
  Rest.liftedBlock (rest_l124c8c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c8c x hx)

theorem rest_l124c92 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124c92 bytes_l124c92) (entryMap (live .l124c92))
      3 0x124c92 bytes_l124c92 b_l124c92 := by
  have f0 : InstrSpec 0x124c92 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x124c92) (movR64R64Effect 0x124c92 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x124c92 0 15).toInstrSpec (mov_r64_r64_effect_step 0x124c92 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124c95 [0x48, 0xB9, 0x15, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124c95) (movR64Imm64Effect 0x124c95 1 0x100000015)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x124c95 1 0x100000015).toInstrSpec (mov_r64_imm64_effect_step 0x124c95 0x48 0xb9 (by decide) (by decide) 0x100000015) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c95) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124c9f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x124c9f 0x7d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124c92 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124c92 :=
  Rest.liftedBlock (rest_l124c92 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124c92 x hx)

theorem rest_l124ca1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124ca1 bytes_l124ca1) (entryMap (live .l124ca1))
      17 0x124ca1 bytes_l124ca1 b_l124ca1 := by
  have f0 : InstrSpec 0x124ca1 [0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x124ca1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124ca1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124ca1 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x124ca1 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x124ca1 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124ca5 [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x124ca5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124ca5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ca5 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124ca5 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x124ca5 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124caa [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x124caa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124caa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124caa 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124caa 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x124caa 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124caf [0x4C, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x124caf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124caf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124caf 8 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x124caf 8 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x124caf 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124cb4 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x124cb4) (movR64R64Effect 0x124cb4 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124cb4 7 14).toInstrSpec (mov_r64_r64_effect_step 0x124cb4 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x124cb7 [0x4D, 0x89, 0x46, 0x30] (StorePre 0x124cb7 4 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x124cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cb7 8 (.base 14 (.d8 0x30)))
      [.gpr 8, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124cb7 8 (.base 14 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x124cb7 0x4d (by decide) 0 (.base 14 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124cbb [0x4C, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x124cbb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124cbb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124cbb 8 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x124cbb 8 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x124cbb 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124cc0 [0x4D, 0x89, 0x46, 0x28] (StorePre 0x124cc0 4 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x124cc0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cc0 8 (.base 14 (.d8 0x28)))
      [.gpr 8, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124cc0 8 (.base 14 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x124cc0 0x4d (by decide) 0 (.base 14 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x124cc4 [0x4C, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x124cc4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x124cc4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124cc4 8 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x124cc4 8 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x124cc4 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x124cc9 [0x4D, 0x89, 0x46, 0x20] (StorePre 0x124cc9 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x124cc9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cc9 8 (.base 14 (.d8 0x20)))
      [.gpr 8, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124cc9 8 (.base 14 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x124cc9 0x4d (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x124ccd [0x4C, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x124ccd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x124ccd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ccd 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x124ccd 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x124ccd 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x124cd2 [0x4D, 0x89, 0x46, 0x18] (StorePre 0x124cd2 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x124cd2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cd2 8 (.base 14 (.d8 0x18)))
      [.gpr 8, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124cd2 8 (.base 14 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x124cd2 0x4d (by decide) 0 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x124cd6 [0x41, 0x89, 0x06] (StorePre 0x124cd6 3 (fun s => AddrMode.addr (.base 14 .none) s (0x124cd6 + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x124cd6 0 (.base 14 .none))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x124cd6 0 (.base 14 .none)).toInstrSpec (mov_m32_r32_effect_step 0x124cd6 0x41 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124cd9 [0x41, 0x89, 0x4E, 0x04] (StorePre 0x124cd9 4 (fun s => AddrMode.addr (.base 14 (.d8 0x4)) s (0x124cd9 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x124cd9 1 (.base 14 (.d8 0x4)))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x124cd9 1 (.base 14 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x124cd9 0x41 (by decide) 1 (.base 14 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x124cdd [0x49, 0x89, 0x56, 0x08] (StorePre 0x124cdd 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x124cdd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124cdd 2 (.base 14 (.d8 0x8)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124cdd 2 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x124cdd 0x49 (by decide) 2 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x124ce1 [0x49, 0x89, 0x76, 0x10] (StorePre 0x124ce1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x124ce1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ce1 6 (.base 14 (.d8 0x10)))
      [.gpr 6, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124ce1 6 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x124ce1 0x49 (by decide) 6 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ca5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124caa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124caf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cb4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cb7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cbb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cc0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cc4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cc9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ccd) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cd2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cd6) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cd9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cdd) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ce1) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 53), (2, 55), (4, 4), (6, 57), (7, 61), (8, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ce5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 77) (jmp_rel32_effect_step 0x124ce5 0xc9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124ca1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124ca1 :=
  Rest.liftedBlock (rest_l124ca1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124ca1 x hx)

theorem rest_l124cea [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124cea bytes_l124cea) (entryMap (live .l124cea))
      4 0x124cea bytes_l124cea b_l124cea := by
  have f0 : InstrSpec 0x124cea [0x48, 0xB9, 0x15, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124cea) (movR64Imm64Effect 0x124cea 1 0x100000015)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x124cea 1 0x100000015).toInstrSpec (mov_r64_imm64_effect_step 0x124cea 0x48 0xb9 (by decide) (by decide) 0x100000015) pre_rip
  have f1 : InstrSpec 0x124cf4 [0x40, 0x84, 0xED] (fun s => s.RIP = 0x124cf4) (testR8R8Effect 0x124cf4 3 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x124cf4 3 5 5).toInstrSpec (test_r8_r8_rex_effect_step 0x124cf4 0x40 0xed (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124cf7 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x124cf7) (movR64R64Effect 0x124cf7 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x124cf7 0 15).toInstrSpec (mov_r64_r64_effect_step 0x124cf7 0x4c 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cf4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cf7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cfa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x124cfa 4 0x14) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124cea [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124cea :=
  Rest.liftedBlock (rest_l124cea code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124cea x hx)

theorem rest_l124cfc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124cfc bytes_l124cfc) (entryMap (live .l124cfc))
      5 0x124cfc bytes_l124cfc b_l124cfc := by
  have f0 : InstrSpec 0x124cfc [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x124cfc) (movR64R64Effect 0x124cfc 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124cfc 7 14).toInstrSpec (mov_r64_r64_effect_step 0x124cfc 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124cff [0x48, 0x8D, 0x51, 0xF0] (fun s => s.RIP = 0x124cff) (leaR64Effect 0x124cff 2 (.base 1 (.d8 0xf0)))
      [.gpr 1] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x124cff 2 (.base 1 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x124cff 0x48 (by decide) 2 (.base 1 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124d03 [0x40, 0x84, 0xED] (fun s => s.RIP = 0x124d03) (testR8R8Effect 0x124d03 3 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x124d03 3 5 5).toInstrSpec (test_r8_r8_rex_effect_step 0x124d03 0x40 0xed (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124d06 [0x48, 0x0F, 0x49, 0xCA] (fun s => s.RIP = 0x124d06) (atFlags (condHolds 9) (cmovR64R64Effect 0x124d06 4 1 2))
      [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x124d06 4 1 2 9).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x124d06 9 0x48 (by decide) 0xca (by decide) c)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124cff) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d03) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d06) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (20, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d0a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 61) (jmp_rel8_effect_step 0x124d0a 0x15 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124cfc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124cfc :=
  Rest.liftedBlock (rest_l124cfc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124cfc x hx)

theorem rest_l124d0c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d0c bytes_l124d0c) (entryMap (live .l124d0c))
      2 0x124d0c bytes_l124d0c b_l124d0c := by
  have f0 : InstrSpec 0x124d0c [0x31, 0xED] (fun s => s.RIP = 0x124d0c) (xorR32R32Effect 0x124d0c 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x124d0c 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x124d0c 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d0e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x124d0e 0x2f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124d0c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d0c :=
  Rest.liftedBlock (rest_l124d0c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d0c x hx)

theorem rest_l124d10 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d10 bytes_l124d10) (entryMap (live .l124d10))
      3 0x124d10 bytes_l124d10 b_l124d10 := by
  have f0 : InstrSpec 0x124d10 [0x0F, 0xB6, 0x6C, 0x24, 0x0D] (LoadPre 0x124d10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x124d10 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x124d10 5 5 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x124d10 5 5 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_effect_step 0x124d10 5 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124d15 [0x40, 0x84, 0xED] (fun s => s.RIP = 0x124d15) (testR8R8Effect 0x124d15 3 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x124d15 3 5 5).toInstrSpec (test_r8_r8_rex_effect_step 0x124d15 0x40 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d15) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d18) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x124d18 8 0x25) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124d10 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d10 :=
  Rest.liftedBlock (rest_l124d10 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d10 x hx)

theorem rest_l124d1a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d1a bytes_l124d1a) (entryMap (live .l124d1a))
      1 0x124d1a bytes_l124d1a b_l124d1a := by
  have f0 : InstrSpec 0x124d1a [0x48, 0x83, 0xC1, 0xF2] (fun s => s.RIP = 0x124d1a) (addR64Imm8Effect 0x124d1a 1 0xf2)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124d1a 1 0xf2).toInstrSpec (add_r64_imm8_effect_step 0x124d1a 0x48 0xc1 0xf2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d1e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l124d1a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d1a :=
  Rest.liftedBlock (rest_l124d1a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d1a x hx)

theorem rest_l124d1e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d1e bytes_l124d1e) (entryMap (live .l124d1e))
      1 0x124d1e bytes_l124d1e b_l124d1e := by
  have f0 : InstrSpec 0x124d1e [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x124d1e) (movR64R64Effect 0x124d1e 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124d1e 7 14).toInstrSpec (mov_r64_r64_effect_step 0x124d1e 0x4c 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d21) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l124d1e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d1e :=
  Rest.liftedBlock (rest_l124d1e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d1e x hx)

theorem rest_l124d21 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d21 bytes_l124d21) (entryMap (live .l124d21))
      7 0x124d21 bytes_l124d21 b_l124d21 := by
  have f0 : InstrSpec 0x124d21 [0xC6, 0x40, 0x20, 0x01] (StorePre 0x124d21 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x124d21 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124d21 (.base 0 (.d8 0x20)) 0x1)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x124d21 (.base 0 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x124d21 (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124d25 [0x8B, 0x40, 0x1C] (LoadPre 0x124d25 (fun s => AddrMode.addr (.base 0 (.d8 0x1c)) s (0x124d25 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x124d25 0 (.base 0 (.d8 0x1c)))
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124d25 0 (.base 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x124d25 0 (.base 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124d28 [0xC7, 0x07, 0x01, 0x00, 0x00, 0x00] (StorePre 0x124d28 6 (fun s => AddrMode.addr (.base 7 .none) s (0x124d28 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124d28 6 (.base 7 .none) 0x1)
      [.gpr 7] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124d28 6 (.base 7 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x124d28 (.base 7 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124d2e [0x89, 0x47, 0x04] (StorePre 0x124d2e 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x124d2e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124d2e 0 (.base 7 (.d8 0x4)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124d2e 0 (.base 7 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x124d2e 0 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124d31 [0x48, 0x89, 0x4F, 0x08] (StorePre 0x124d31 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x124d31 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d31 1 (.base 7 (.d8 0x8)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x124d31 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x124d31 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124d35 [0x48, 0xC7, 0x47, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x124d35 8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x124d35 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x124d35 (.base 7 (.d8 0x10)) 0x0)
      [.gpr 7] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x124d35 (.base 7 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x124d35 0x48 (by decide) (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d25) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d28) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d2e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d31) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d35) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d3d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 60) (jmp_rel8_effect_step 0x124d3d 0x74 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124d21 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d21 :=
  Rest.liftedBlock (rest_l124d21 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d21 x hx)

theorem rest_l124d3f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d3f bytes_l124d3f) (entryMap (live .l124d3f))
      4 0x124d3f bytes_l124d3f b_l124d3f := by
  have f0 : InstrSpec 0x124d3f [0x40, 0x88, 0x6C, 0x24, 0x0F] (StorePre 0x124d3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x124d3f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x124d3f 5 5 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x124d3f 5 5 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x124d3f 0x40 (by decide) 5 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124d44 [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x124d44) (leaR64Effect 0x124d44 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124d44 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x124d44 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124d49 [0x48, 0x8D, 0x74, 0x24, 0x0F] (fun s => s.RIP = 0x124d49) (leaR64Effect 0x124d49 6 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x124d49 6 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x124d49 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124d4e [0xE8, 0x1D, 0x29, 0x00, 0x00] (PushPre 0x124d4e 5) (callEffect (fun _ => 0x127670) 0x124d53)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124d4e 0x127670 0x124d53).toInstrSpec (call_rel32_effect_step 0x124d4e 0x291d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d44) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d49) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d4e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (3, 3), (4, 58), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127670) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 60) (by decide) (by decide) rfl rfl

theorem block_l124d3f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d3f :=
  Rest.liftedBlock (rest_l124d3f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d3f x hx)

theorem rest_l124d53 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d53 bytes_l124d53) (entryMap (live .l124d53))
      4 0x124d53 bytes_l124d53 b_l124d53 := by
  have f0 : InstrSpec 0x124d53 [0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x124d53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124d53 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124d53 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x124d53 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x124d53 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124d57 [0x8B, 0x44, 0x24, 0x14] (LoadPre 0x124d57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124d57 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124d57 0 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124d57 0 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x124d57 0 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124d5b [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x124d5b) (cmpR32Imm8Effect 0x124d5b 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124d5b 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124d5b 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d57) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d5b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d5e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x124d5e 5 0x13) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124d53 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d53 :=
  Rest.liftedBlock (rest_l124d53 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d53 x hx)

theorem rest_l124d60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d60 bytes_l124d60) (entryMap (live .l124d60))
      3 0x124d60 bytes_l124d60 b_l124d60 := by
  have f0 : InstrSpec 0x124d60 [0x39, 0xC3] (fun s => s.RIP = 0x124d60) (cmpR32R32Effect 0x124d60 2 3 0)
      [.gpr 3, .gpr 0] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x124d60 2 3 0).toInstrSpec (cmp_r32_r32_effect_step 0x124d60 0xc3 (by decide)) pre_rip
  have f1 : InstrSpec 0x124d62 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x124d62) (movR64R64Effect 0x124d62 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124d62 7 14).toInstrSpec (mov_r64_r64_effect_step 0x124d62 0x4c 0xf7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d62) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d65) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x124d65 5 0x5a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124d60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d60 :=
  Rest.liftedBlock (rest_l124d60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d60 x hx)

theorem rest_l124d67 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d67 bytes_l124d67) (entryMap (live .l124d67))
      3 0x124d67 bytes_l124d67 b_l124d67 := by
  have f0 : InstrSpec 0x124d67 [0x40, 0x88, 0x6F, 0x04] (StorePre 0x124d67 4 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x124d67 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x124d67 4 5 (.base 7 (.d8 0x4)))
      [.gpr 5, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x124d67 4 5 (.base 7 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x124d67 0x40 (by decide) 5 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124d6b [0xC7, 0x07, 0x02, 0x00, 0x00, 0x00] (StorePre 0x124d6b 6 (fun s => AddrMode.addr (.base 7 .none) s (0x124d6b + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124d6b 6 (.base 7 .none) 0x2)
      [.gpr 7] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124d6b 6 (.base 7 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x124d6b (.base 7 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d6b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d71) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x124d71 0x40 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124d67 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d67 :=
  Rest.liftedBlock (rest_l124d67 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d67 x hx)

theorem rest_l124d73 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124d73 bytes_l124d73) (entryMap (live .l124d73))
      15 0x124d73 bytes_l124d73 b_l124d73 := by
  have f0 : InstrSpec 0x124d73 [0x48, 0x8B, 0x54, 0x24, 0x40] (LoadPre 0x124d73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x124d73 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d73 2 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124d73 2 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x124d73 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124d78 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x124d78) (movR64R64Effect 0x124d78 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124d78 7 14).toInstrSpec (mov_r64_r64_effect_step 0x124d78 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124d7b [0x49, 0x89, 0x56, 0x30] (StorePre 0x124d7b 4 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x124d7b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d7b 2 (.base 14 (.d8 0x30)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124d7b 2 (.base 14 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x124d7b 0x49 (by decide) 2 (.base 14 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124d7f [0x48, 0x8B, 0x54, 0x24, 0x38] (LoadPre 0x124d7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x124d7f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d7f 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124d7f 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x124d7f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124d84 [0x49, 0x89, 0x56, 0x28] (StorePre 0x124d84 4 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x124d84 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d84 2 (.base 14 (.d8 0x28)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124d84 2 (.base 14 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x124d84 0x49 (by decide) 2 (.base 14 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124d88 [0x48, 0x8B, 0x54, 0x24, 0x30] (LoadPre 0x124d88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x124d88 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d88 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124d88 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x124d88 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x124d8d [0x49, 0x89, 0x56, 0x20] (StorePre 0x124d8d 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x124d8d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d8d 2 (.base 14 (.d8 0x20)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124d8d 2 (.base 14 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x124d8d 0x49 (by decide) 2 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x124d91 [0x48, 0x8B, 0x54, 0x24, 0x28] (LoadPre 0x124d91 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x124d91 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d91 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124d91 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x124d91 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x124d96 [0x49, 0x89, 0x56, 0x18] (StorePre 0x124d96 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x124d96 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124d96 2 (.base 14 (.d8 0x18)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124d96 2 (.base 14 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x124d96 0x49 (by decide) 2 (.base 14 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x124d9a [0x48, 0x8B, 0x54, 0x24, 0x18] (LoadPre 0x124d9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x124d9a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d9a 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124d9a 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x124d9a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x124d9f [0x48, 0x8B, 0x74, 0x24, 0x20] (LoadPre 0x124d9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x124d9f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124d9f 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124d9f 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x124d9f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x124da4 [0x49, 0x89, 0x76, 0x10] (StorePre 0x124da4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x124da4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124da4 6 (.base 14 (.d8 0x10)))
      [.gpr 6, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124da4 6 (.base 14 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x124da4 0x49 (by decide) 6 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x124da8 [0x49, 0x89, 0x56, 0x08] (StorePre 0x124da8 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x124da8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124da8 2 (.base 14 (.d8 0x8)))
      [.gpr 2, .gpr 14] [] [.rip] :=
    (movM64R64Effect_footprint 0x124da8 2 (.base 14 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x124da8 0x49 (by decide) 2 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124dac [0x41, 0x89, 0x0E] (StorePre 0x124dac 3 (fun s => AddrMode.addr (.base 14 .none) s (0x124dac + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x124dac 1 (.base 14 .none))
      [.gpr 1, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x124dac 1 (.base 14 .none)).toInstrSpec (mov_m32_r32_effect_step 0x124dac 0x41 (by decide) 1 (.base 14 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x124daf [0x41, 0x89, 0x46, 0x04] (StorePre 0x124daf 4 (fun s => AddrMode.addr (.base 14 (.d8 0x4)) s (0x124daf + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x124daf 0 (.base 14 (.d8 0x4)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM32R32Effect_footprint 0x124daf 0 (.base 14 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x124daf 0x41 (by decide) 0 (.base 14 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d78) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d7b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d7f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 58), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d84) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 58), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d88) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d8d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 61), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d91) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 64), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d96) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 64), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d9a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 67), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124d9f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 67), (4, 4), (6, 69), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124da4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 67), (4, 4), (6, 69), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124da8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 67), (4, 4), (6, 69), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124dac) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 67), (4, 4), (6, 69), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124daf) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 67), (4, 4), (6, 69), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124db3) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 75) (by decide) rfl

theorem block_l124d73 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124d73 :=
  Rest.liftedBlock (rest_l124d73 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124d73 x hx)

theorem rest_l124db3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124db3 bytes_l124db3) (entryMap (live .l124db3))
      7 0x124db3 bytes_l124db3 b_l124db3 := by
  have f0 : InstrSpec 0x124db3 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x124db3) (movR64R64Effect 0x124db3 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x124db3 0 7).toInstrSpec (mov_r64_r64_effect_step 0x124db3 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124db6 [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x124db6) (addR64Imm8Effect 0x124db6 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124db6 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x124db6 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124dba [0x5B] (PopPre 0x124dba) (popR64Effect 0x124dba 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124dba 1 3).toInstrSpec (pop_r64_effect_step 0x124dba 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124dbb [0x41, 0x5E] (PopPre 0x124dbb) (popR64Effect 0x124dbb 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124dbb 2 14).toInstrSpec (pop_r64_rex_effect_step 0x124dbb 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124dbd [0x41, 0x5F] (PopPre 0x124dbd) (popR64Effect 0x124dbd 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124dbd 2 15).toInstrSpec (pop_r64_rex_effect_step 0x124dbd 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x124dbf [0x5D] (PopPre 0x124dbf) (popR64Effect 0x124dbf 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124dbf 1 5).toInstrSpec (pop_r64_effect_step 0x124dbf 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x124dc0 [0xC3] (RetPre 0x124dc0) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x124dc0).toInstrSpec (ret_effect_step 0x124dc0) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124db6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124dba) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124dbb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124dbd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124dbf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124dc0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (5, 66), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l124db3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124db3 :=
  Rest.liftedBlock (rest_l124db3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124db3 x hx)

theorem rest_l124dc1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124dc1 bytes_l124dc1) (entryMap (live .l124dc1))
      3 0x124dc1 bytes_l124dc1 b_l124dc1 := by
  have f0 : InstrSpec 0x124dc1 [0x41, 0xC6, 0x47, 0x20, 0x01] (StorePre 0x124dc1 5 (fun s => AddrMode.addr (.base 15 (.d8 0x20)) s (0x124dc1 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x124dc1 (.base 15 (.d8 0x20)) 0x1)
      [.gpr 15] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x124dc1 (.base 15 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x124dc1 0x41 (by decide) (.base 15 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x124dc6 [0x41, 0x8B, 0x47, 0x1C] (LoadPre 0x124dc6 (fun s => AddrMode.addr (.base 15 (.d8 0x1c)) s (0x124dc6 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x124dc6 0 (.base 15 (.d8 0x1c)))
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32M32Effect_footprint 0x124dc6 0 (.base 15 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x124dc6 0x41 (by decide) 0 (.base 15 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124dc6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124dca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 56) (jmp_rel32_effect_step 0x124dca 0xfffffe36 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124dc1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124dc1 :=
  Rest.liftedBlock (rest_l124dc1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124dc1 x hx)

theorem rest_l124dcf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124dcf bytes_l124dcf) (entryMap (live .l124dcf))
      3 0x124dcf bytes_l124dcf b_l124dcf := by
  have f0 : InstrSpec 0x124dcf [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x124dcf) (movR64R64Effect 0x124dcf 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124dcf 7 3).toInstrSpec (mov_r64_r64_effect_step 0x124dcf 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124dd2 [0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x124dd2) (movR64Imm32Effect 0x124dd2 2 0x2036e0)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x124dd2 2 0x2036e0).toInstrSpec (mov_r64_imm32_effect_step 0x124dd2 0x48 0xc2 (by decide) (by decide) (by decide) 0x2036e0) pre_rip
  have f2 : InstrSpec 0x124dd9 [0xE8, 0xB2, 0x4E, 0x00, 0x00] (PushPre 0x124dd9 5) (callEffect (fun _ => 0x129c90) 0x124dde)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124dd9 0x129c90 0x124dde).toInstrSpec (call_rel32_effect_step 0x124dd9 0x4eb2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x124dd2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x124dd9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x129c90) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l124dcf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124dcf :=
  Rest.liftedBlock (rest_l124dcf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124dcf x hx)

theorem rest_l124dde [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124dde bytes_l124dde) (entryMap (live .l124dde))
      1 0x124dde bytes_l124dde b_l124dde := by
  have f0 : InstrSpec 0x124dde [0x66, 0x90] (fun s => s.RIP = 0x124dde) (fun _ => nopEffect 0x124dde 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x124dde 2).toInstrSpec (nop_66_effect_step 0x124dde) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124de0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l124dde [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124dde :=
  Rest.liftedBlock (rest_l124dde code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124dde x hx)

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

theorem_by block_l124be0_eval :
    program.runBlock (dialect code) ⟨.l124be0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124bf9_eval :
    program.runBlock (dialect code) ⟨.l124bf9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124bfe_eval :
    program.runBlock (dialect code) ⟨.l124bfe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c05_eval :
    program.runBlock (dialect code) ⟨.l124c05, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c1f_eval :
    program.runBlock (dialect code) ⟨.l124c1f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c3c_eval :
    program.runBlock (dialect code) ⟨.l124c3c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c4e_eval :
    program.runBlock (dialect code) ⟨.l124c4e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c57_eval :
    program.runBlock (dialect code) ⟨.l124c57, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c65_eval :
    program.runBlock (dialect code) ⟨.l124c65, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c78_eval :
    program.runBlock (dialect code) ⟨.l124c78, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c83_eval :
    program.runBlock (dialect code) ⟨.l124c83, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c8c_eval :
    program.runBlock (dialect code) ⟨.l124c8c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124c92_eval :
    program.runBlock (dialect code) ⟨.l124c92, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124ca1_eval :
    program.runBlock (dialect code) ⟨.l124ca1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124cea_eval :
    program.runBlock (dialect code) ⟨.l124cea, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124cfc_eval :
    program.runBlock (dialect code) ⟨.l124cfc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d0c_eval :
    program.runBlock (dialect code) ⟨.l124d0c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d10_eval :
    program.runBlock (dialect code) ⟨.l124d10, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d1a_eval :
    program.runBlock (dialect code) ⟨.l124d1a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d1e_eval :
    program.runBlock (dialect code) ⟨.l124d1e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d21_eval :
    program.runBlock (dialect code) ⟨.l124d21, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d3f_eval :
    program.runBlock (dialect code) ⟨.l124d3f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d53_eval :
    program.runBlock (dialect code) ⟨.l124d53, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d60_eval :
    program.runBlock (dialect code) ⟨.l124d60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d67_eval :
    program.runBlock (dialect code) ⟨.l124d67, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124d73_eval :
    program.runBlock (dialect code) ⟨.l124d73, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124db3_eval :
    program.runBlock (dialect code) ⟨.l124db3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124dc1_eval :
    program.runBlock (dialect code) ⟨.l124dc1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124dcf_eval :
    program.runBlock (dialect code) ⟨.l124dcf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124dde_eval :
    program.runBlock (dialect code) ⟨.l124dde, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Generate.LIR
