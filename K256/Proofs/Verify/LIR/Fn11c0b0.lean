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

theorem rest_l11c0b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c0b0 bytes_l11c0b0) (entryMap (live .l11c0b0))
      5 0x11c0b0 bytes_l11c0b0 b_l11c0b0 := by
  have f0 : InstrSpec 0x11c0b0 [0x53] (PushPre 0x11c0b0 1) (pushR64Effect 0x11c0b0 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11c0b0 1 3).toInstrSpec (push_r64_effect_step 0x11c0b0 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x11c0b1 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x11c0b1) (movR64R64Effect 0x11c0b1 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c0b1 0 6).toInstrSpec (mov_r64_r64_effect_step 0x11c0b1 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c0b4 [0x48, 0x8B, 0x0F] (LoadPre 0x11c0b4 (fun s => AddrMode.addr (.base 7 .none) s (0x11c0b4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c0b4 1 (.base 7 .none))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c0b4 1 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c0b4 0x48 (by decide) 1 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11c0b7 [0x48, 0x83, 0x7F, 0x10, 0x00] (LoadPre 0x11c0b7 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x11c0b7 + BitVec.ofNat 64 5)) 8) (cmpMImm8Effect 0x11c0b7 5 64 (.base 7 (.d8 0x10)) 0x0)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpMImm8Effect64_footprint 0x11c0b7 5 (.base 7 (.d8 0x10)) 0x0).toInstrSpec (cmp_m64_imm8_effect_step 0x11c0b7 0x48 (by decide) (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0b4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0b7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0bc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x11c0bc 4 0xf8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c0b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c0b0 :=
  Rest.liftedBlock (rest_l11c0b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c0b0 x hx)

theorem rest_l11c0c2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c0c2 bytes_l11c0c2) (entryMap (live .l11c0c2))
      5 0x11c0c2 bytes_l11c0c2 b_l11c0c2 := by
  have f0 : InstrSpec 0x11c0c2 [0x4C, 0x8B, 0x57, 0x30] (LoadPre 0x11c0c2 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x11c0c2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c0c2 10 (.base 7 (.d8 0x30)))
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11c0c2 10 (.base 7 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x11c0c2 0x4c (by decide) 2 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c0c6 [0x4C, 0x8B, 0x5F, 0x38] (LoadPre 0x11c0c6 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x11c0c6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c0c6 11 (.base 7 (.d8 0x38)))
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11c0c6 11 (.base 7 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x11c0c6 0x4c (by decide) 3 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c0ca [0x4D, 0x89, 0xD9] (fun s => s.RIP = 0x11c0ca) (movR64R64Effect 0x11c0ca 9 11)
      [.gpr 11] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x11c0ca 9 11).toInstrSpec (mov_r64_r64_effect_step 0x11c0ca 0x4d 0xd9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c0cd [0x4D, 0x29, 0xD1] (fun s => s.RIP = 0x11c0cd) (subR64R64Effect 0x11c0cd 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11c0cd 9 10).toInstrSpec (sub_r64_r64_effect_step 0x11c0cd 0x4d 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0c6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0ca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0cd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 59), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0d0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel32_effect_step 0x11c0d0 4 0xe4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c0c2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c0c2 :=
  Rest.liftedBlock (rest_l11c0c2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c0c2 x hx)

theorem rest_l11c0d6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c0d6 bytes_l11c0d6) (entryMap (live .l11c0d6))
      7 0x11c0d6 bytes_l11c0d6 b_l11c0d6 := by
  have f0 : InstrSpec 0x11c0d6 [0x48, 0x8B, 0x57, 0x20] (LoadPre 0x11c0d6 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x11c0d6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c0d6 2 (.base 7 (.d8 0x20)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11c0d6 2 (.base 7 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11c0d6 0x48 (by decide) 2 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c0da [0x49, 0x69, 0xF2, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c0da) (imulR64R64Imm32Effect 0x11c0da 7 6 10 0x110)
      [.gpr 10] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x11c0da 7 6 10 0x110).toInstrSpec (imul_r64_r64_imm32_effect_step 0x11c0da 0x49 (by decide) 0xf2 (by decide) 0x110) pre_rip
  have f2 : InstrSpec 0x11c0e1 [0x45, 0x89, 0xC8] (fun s => s.RIP = 0x11c0e1) (movR32R32Effect 0x11c0e1 3 8 9)
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x11c0e1 3 8 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x11c0e1 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c0e4 [0x41, 0x83, 0xE0, 0x03] (fun s => s.RIP = 0x11c0e4) (andR32Imm8Effect 0x11c0e4 4 8 0x3)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x11c0e4 4 8 0x3).toInstrSpec (and_r32_imm8_rex_effect_step 0x11c0e4 0x41 0xe0 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c0e8 [0x4D, 0x29, 0xDA] (fun s => s.RIP = 0x11c0e8) (subR64R64Effect 0x11c0e8 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11c0e8 10 11).toInstrSpec (sub_r64_r64_effect_step 0x11c0e8 0x4d 0xda (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c0eb [0x49, 0x83, 0xFA, 0xFC] (fun s => s.RIP = 0x11c0eb) (cmpR64Imm8Effect 0x11c0eb 10 0xfc)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x11c0eb 10 0xfc).toInstrSpec (cmp_r64_imm8_effect_step 0x11c0eb 0x49 0xfa 0xfc (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0da) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0e1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0e4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0e8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (8, 59), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0eb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (8, 59), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0ef) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x11c0ef 6 0x8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c0d6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c0d6 :=
  Rest.liftedBlock (rest_l11c0d6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c0d6 x hx)

theorem rest_l11c0f1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c0f1 bytes_l11c0f1) (entryMap (live .l11c0f1))
      2 0x11c0f1 bytes_l11c0f1 b_l11c0f1 := by
  have f0 : InstrSpec 0x11c0f1 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x11c0f1) (xorR32R32Effect 0x11c0f1 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c0f1 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x11c0f1 0x45 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0f4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x11c0f4 0x8e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c0f1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c0f1 :=
  Rest.liftedBlock (rest_l11c0f1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c0f1 x hx)

theorem rest_l11c0f9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c0f9 bytes_l11c0f9) (entryMap (live .l11c0f9))
      4 0x11c0f9 bytes_l11c0f9 b_l11c0f9 := by
  have f0 : InstrSpec 0x11c0f9 [0x4C, 0x8D, 0x1C, 0x32] (fun s => s.RIP = 0x11c0f9) (leaR64Effect 0x11c0f9 11 (.sib 2 (some 6) 0 .none))
      [.gpr 2, .gpr 6] [] [.reg 11, .rip] :=
    (leaR64Effect_footprint 0x11c0f9 11 (.sib 2 (some 6) 0 .none)).toInstrSpec (lea_r64_effect_step 0x11c0f9 0x4c (by decide) 3 (.sib 2 (some 6) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c0fd [0x49, 0x83, 0xE1, 0xFC] (fun s => s.RIP = 0x11c0fd) (andR64Imm8Effect 0x11c0fd 9 0xfc)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x11c0fd 9 0xfc).toInstrSpec (and_r64_imm8_effect_step 0x11c0fd 0x49 0xe1 0xfc (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c101 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x11c101) (xorR32R32Effect 0x11c101 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c101 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x11c101 0x45 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c0fd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c101) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 57), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c104) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x11c104 0x1a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c0f9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c0f9 :=
  Rest.liftedBlock (rest_l11c0f9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c0f9 x hx)

theorem rest_l11c110 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c110 bytes_l11c110) (entryMap (live .l11c110))
      4 0x11c110 bytes_l11c110 b_l11c110 := by
  have f0 : InstrSpec 0x11c110 [0x49, 0x83, 0xC2, 0x04] (fun s => s.RIP = 0x11c110) (addR64Imm8Effect 0x11c110 10 0x4)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11c110 10 0x4).toInstrSpec (add_r64_imm8_effect_step 0x11c110 0x49 0xc2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c114 [0x49, 0x81, 0xC3, 0x40, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x11c114) (addR64Imm32Effect 0x11c114 11 0x440)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11c114 11 0x440).toInstrSpec (add_r64_imm32_effect_step 0x11c114 0x49 0xc3 0x440 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c11b [0x4D, 0x39, 0xD1] (fun s => s.RIP = 0x11c11b) (cmpR64R64Effect 0x11c11b 9 10)
      [.gpr 9, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c11b 9 10).toInstrSpec (cmp_r64_r64_effect_step 0x11c11b 0x4d 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c114) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c11b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c11e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x11c11e 4 0x62) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c110 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c110 :=
  Rest.liftedBlock (rest_l11c110 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c110 x hx)

theorem rest_l11c120 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c120 bytes_l11c120) (entryMap (live .l11c120))
      3 0x11c120 bytes_l11c120 b_l11c120 := by
  have f0 : InstrSpec 0x11c120 [0x49, 0x8B, 0x1B] (LoadPre 0x11c120 (fun s => AddrMode.addr (.base 11 .none) s (0x11c120 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c120 3 (.base 11 .none))
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11c120 3 (.base 11 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c120 0x49 (by decide) 3 (.base 11 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c123 [0x48, 0x39, 0xD8] (fun s => s.RIP = 0x11c123) (cmpR64R64Effect 0x11c123 0 3)
      [.gpr 0, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c123 0 3).toInstrSpec (cmp_r64_r64_effect_step 0x11c123 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c123) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c126) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c126 6 0x28) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c120 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c120 :=
  Rest.liftedBlock (rest_l11c120 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c120 x hx)

theorem rest_l11c128 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c128 bytes_l11c128) (entryMap (live .l11c128))
      3 0x11c128 bytes_l11c128 b_l11c128 := by
  have f0 : InstrSpec 0x11c128 [0x49, 0x8B, 0x9B, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x11c128 (fun s => AddrMode.addr (.base 11 (.d32 0x110)) s (0x11c128 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c128 3 (.base 11 (.d32 0x110)))
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11c128 3 (.base 11 (.d32 0x110))).toInstrSpec (mov_r64_m64_effect_step 0x11c128 0x49 (by decide) 3 (.base 11 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c12f [0x48, 0x39, 0xD8] (fun s => s.RIP = 0x11c12f) (cmpR64R64Effect 0x11c12f 0 3)
      [.gpr 0, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c12f 0 3).toInstrSpec (cmp_r64_r64_effect_step 0x11c12f 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c12f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c132) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c132 6 0x2b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c128 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c128 :=
  Rest.liftedBlock (rest_l11c128 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c128 x hx)

theorem rest_l11c134 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c134 bytes_l11c134) (entryMap (live .l11c134))
      3 0x11c134 bytes_l11c134 b_l11c134 := by
  have f0 : InstrSpec 0x11c134 [0x49, 0x8B, 0x9B, 0x20, 0x02, 0x00, 0x00] (LoadPre 0x11c134 (fun s => AddrMode.addr (.base 11 (.d32 0x220)) s (0x11c134 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c134 3 (.base 11 (.d32 0x220)))
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11c134 3 (.base 11 (.d32 0x220))).toInstrSpec (mov_r64_m64_effect_step 0x11c134 0x49 (by decide) 3 (.base 11 (.d32 0x220)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c13b [0x48, 0x39, 0xD8] (fun s => s.RIP = 0x11c13b) (cmpR64R64Effect 0x11c13b 0 3)
      [.gpr 0, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c13b 0 3).toInstrSpec (cmp_r64_r64_effect_step 0x11c13b 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c13b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c13e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c13e 6 0x2e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c134 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c134 :=
  Rest.liftedBlock (rest_l11c134 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c134 x hx)

theorem rest_l11c140 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c140 bytes_l11c140) (entryMap (live .l11c140))
      3 0x11c140 bytes_l11c140 b_l11c140 := by
  have f0 : InstrSpec 0x11c140 [0x49, 0x8B, 0x9B, 0x30, 0x03, 0x00, 0x00] (LoadPre 0x11c140 (fun s => AddrMode.addr (.base 11 (.d32 0x330)) s (0x11c140 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c140 3 (.base 11 (.d32 0x330)))
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11c140 3 (.base 11 (.d32 0x330))).toInstrSpec (mov_r64_m64_effect_step 0x11c140 0x49 (by decide) 3 (.base 11 (.d32 0x330)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c147 [0x48, 0x39, 0xD8] (fun s => s.RIP = 0x11c147) (cmpR64R64Effect 0x11c147 0 3)
      [.gpr 0, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c147 0 3).toInstrSpec (cmp_r64_r64_effect_step 0x11c147 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c147) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c14a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c14a 7 0xc4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c140 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c140 :=
  Rest.liftedBlock (rest_l11c140 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c140 x hx)

theorem rest_l11c14c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c14c bytes_l11c14c) (entryMap (live .l11c14c))
      1 0x11c14c bytes_l11c14c b_l11c14c := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x11c14c 0x2f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c14c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c14c :=
  Rest.liftedBlock (rest_l11c14c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c14c x hx)

theorem rest_l11c150 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c150 bytes_l11c150) (entryMap (live .l11c150))
      4 0x11c150 bytes_l11c150 b_l11c150 := by
  have f0 : InstrSpec 0x11c150 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x11c150) (movR64R64Effect 0x11c150 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c150 0 3).toInstrSpec (mov_r64_r64_effect_step 0x11c150 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c153 [0x49, 0x8B, 0x9B, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x11c153 (fun s => AddrMode.addr (.base 11 (.d32 0x110)) s (0x11c153 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c153 3 (.base 11 (.d32 0x110)))
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11c153 3 (.base 11 (.d32 0x110))).toInstrSpec (mov_r64_m64_effect_step 0x11c153 0x49 (by decide) 3 (.base 11 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c15a [0x48, 0x39, 0xD8] (fun s => s.RIP = 0x11c15a) (cmpR64R64Effect 0x11c15a 0 3)
      [.gpr 0, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c15a 0 3).toInstrSpec (cmp_r64_r64_effect_step 0x11c15a 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c153) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c15a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c15d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x11c15d 7 0xd5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c150 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c150 :=
  Rest.liftedBlock (rest_l11c150 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c150 x hx)

theorem rest_l11c15f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c15f bytes_l11c15f) (entryMap (live .l11c15f))
      4 0x11c15f bytes_l11c15f b_l11c15f := by
  have f0 : InstrSpec 0x11c15f [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x11c15f) (movR64R64Effect 0x11c15f 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c15f 0 3).toInstrSpec (mov_r64_r64_effect_step 0x11c15f 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c162 [0x49, 0x8B, 0x9B, 0x20, 0x02, 0x00, 0x00] (LoadPre 0x11c162 (fun s => AddrMode.addr (.base 11 (.d32 0x220)) s (0x11c162 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c162 3 (.base 11 (.d32 0x220)))
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11c162 3 (.base 11 (.d32 0x220))).toInstrSpec (mov_r64_m64_effect_step 0x11c162 0x49 (by decide) 3 (.base 11 (.d32 0x220)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c169 [0x48, 0x39, 0xD8] (fun s => s.RIP = 0x11c169) (cmpR64R64Effect 0x11c169 0 3)
      [.gpr 0, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c169 0 3).toInstrSpec (cmp_r64_r64_effect_step 0x11c169 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c162) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c169) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c16c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x11c16c 7 0xd2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c15f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c15f :=
  Rest.liftedBlock (rest_l11c15f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c15f x hx)

theorem rest_l11c16e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c16e bytes_l11c16e) (entryMap (live .l11c16e))
      4 0x11c16e bytes_l11c16e b_l11c16e := by
  have f0 : InstrSpec 0x11c16e [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x11c16e) (movR64R64Effect 0x11c16e 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c16e 0 3).toInstrSpec (mov_r64_r64_effect_step 0x11c16e 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c171 [0x49, 0x8B, 0x9B, 0x30, 0x03, 0x00, 0x00] (LoadPre 0x11c171 (fun s => AddrMode.addr (.base 11 (.d32 0x330)) s (0x11c171 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c171 3 (.base 11 (.d32 0x330)))
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x11c171 3 (.base 11 (.d32 0x330))).toInstrSpec (mov_r64_m64_effect_step 0x11c171 0x49 (by decide) 3 (.base 11 (.d32 0x330)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c178 [0x48, 0x39, 0xD8] (fun s => s.RIP = 0x11c178) (cmpR64R64Effect 0x11c178 0 3)
      [.gpr 0, .gpr 3] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c178 0 3).toInstrSpec (cmp_r64_r64_effect_step 0x11c178 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c171) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c178) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c17b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x11c17b 7 0x93) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c16e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c16e :=
  Rest.liftedBlock (rest_l11c16e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c16e x hx)

theorem rest_l11c17d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c17d bytes_l11c17d) (entryMap (live .l11c17d))
      2 0x11c17d bytes_l11c17d b_l11c17d := by
  have f0 : InstrSpec 0x11c17d [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x11c17d) (movR64R64Effect 0x11c17d 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c17d 0 3).toInstrSpec (mov_r64_r64_effect_step 0x11c17d 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c180) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x11c180 0x8e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c17d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c17d :=
  Rest.liftedBlock (rest_l11c17d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c17d x hx)

theorem rest_l11c182 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c182 bytes_l11c182) (entryMap (live .l11c182))
      2 0x11c182 bytes_l11c182 b_l11c182 := by
  have f0 : InstrSpec 0x11c182 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x11c182) (testR64R64Effect 0x11c182 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11c182 8 8).toInstrSpec (test_r64_r64_effect_step 0x11c182 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c185) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x11c185 4 0x33) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c182 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c182 :=
  Rest.liftedBlock (rest_l11c182 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c182 x hx)

theorem rest_l11c187 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c187 bytes_l11c187) (entryMap (live .l11c187))
      6 0x11c187 bytes_l11c187 b_l11c187 := by
  have f0 : InstrSpec 0x11c187 [0x4D, 0x69, 0xCA, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c187) (imulR64R64Imm32Effect 0x11c187 7 9 10 0x110)
      [.gpr 10] [] [.reg 9, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x11c187 7 9 10 0x110).toInstrSpec (imul_r64_r64_imm32_effect_step 0x11c187 0x4d (by decide) 0xca (by decide) 0x110) pre_rip
  have f1 : InstrSpec 0x11c18e [0x4C, 0x01, 0xCA] (fun s => s.RIP = 0x11c18e) (addR64R64Effect 0x11c18e 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c18e 2 9).toInstrSpec (add_r64_r64_effect_step 0x11c18e 0x4c 0xca (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c191 [0x48, 0x01, 0xF2] (fun s => s.RIP = 0x11c191) (addR64R64Effect 0x11c191 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c191 2 6).toInstrSpec (add_r64_r64_effect_step 0x11c191 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c194 [0x49, 0x69, 0xF0, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c194) (imulR64R64Imm32Effect 0x11c194 7 6 8 0x110)
      [.gpr 8] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x11c194 7 6 8 0x110).toInstrSpec (imul_r64_r64_imm32_effect_step 0x11c194 0x49 (by decide) 0xf0 (by decide) 0x110) pre_rip
  have f4 : InstrSpec 0x11c19b [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x11c19b) (xorR32R32Effect 0x11c19b 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c19b 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x11c19b 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c19e [0x66, 0x90] (fun s => s.RIP = 0x11c19e) (fun _ => nopEffect 0x11c19e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11c19e 2).toInstrSpec (nop_66_effect_step 0x11c19e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c18e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c191) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c194) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c19b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (5, 5), (6, 59), (7, 7), (8, 61), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c19e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 57), (4, 4), (5, 5), (6, 59), (7, 7), (8, 61), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1a0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 64) (by decide) rfl

theorem block_l11c187 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c187 :=
  Rest.liftedBlock (rest_l11c187 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c187 x hx)

theorem rest_l11c1a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c1a0 bytes_l11c1a0) (entryMap (live .l11c1a0))
      7 0x11c1a0 bytes_l11c1a0 b_l11c1a0 := by
  have f0 : InstrSpec 0x11c1a0 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x11c1a0) (movR64R64Effect 0x11c1a0 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x11c1a0 9 0).toInstrSpec (mov_r64_r64_effect_step 0x11c1a0 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c1a3 [0x4A, 0x8B, 0x04, 0x02] (LoadPre 0x11c1a3 (fun s => AddrMode.addr (.sib 2 (some 8) 0 .none) s (0x11c1a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c1a3 0 (.sib 2 (some 8) 0 .none))
      [.gpr 2, .gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11c1a3 0 (.sib 2 (some 8) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c1a3 0x4a (by decide) 0 (.sib 2 (some 8) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c1a7 [0x49, 0x39, 0xC1] (fun s => s.RIP = 0x11c1a7) (cmpR64R64Effect 0x11c1a7 9 0)
      [.gpr 9, .gpr 0] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c1a7 9 0).toInstrSpec (cmp_r64_r64_effect_step 0x11c1a7 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c1aa [0x49, 0x0F, 0x47, 0xC1] (fun s => s.RIP = 0x11c1aa) (atFlags (condHolds 7) (cmovR64R64Effect 0x11c1aa 4 0 9))
      [.gpr 0, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (cmovR64R64Effect_footprint 0x11c1aa 4 0 9 7).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11c1aa 7 0x49 (by decide) 0xc1 (by decide) c)) pre_rip
  have f4 : InstrSpec 0x11c1ae [0x49, 0x81, 0xC0, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c1ae) (addR64Imm32Effect 0x11c1ae 8 0x110)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11c1ae 8 0x110).toInstrSpec (add_r64_imm32_effect_step 0x11c1ae 0x49 0xc0 0x110 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c1b5 [0x4C, 0x39, 0xC6] (fun s => s.RIP = 0x11c1b5) (cmpR64R64Effect 0x11c1b5 6 8)
      [.gpr 6, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c1b5 6 8).toInstrSpec (cmp_r64_r64_effect_step 0x11c1b5 0x4c 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1aa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1ae) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1b5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 62), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1b8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x11c1b8 5 0xe6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c1a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c1a0 :=
  Rest.liftedBlock (rest_l11c1a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c1a0 x hx)

theorem rest_l11c1ba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c1ba bytes_l11c1ba) (entryMap (live .l11c1ba))
      3 0x11c1ba bytes_l11c1ba b_l11c1ba := by
  have f0 : InstrSpec 0x11c1ba [0x48, 0x8B, 0x57, 0x40] (LoadPre 0x11c1ba (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x11c1ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c1ba 2 (.base 7 (.d8 0x40)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11c1ba 2 (.base 7 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x11c1ba 0x48 (by decide) 2 (.base 7 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c1be [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x11c1be) (testR64R64Effect 0x11c1be 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11c1be 1 1).toInstrSpec (test_r64_r64_effect_step 0x11c1be 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1be) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1c1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x11c1c1 4 0xf5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c1ba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c1ba :=
  Rest.liftedBlock (rest_l11c1ba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c1ba x hx)

theorem rest_l11c1c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c1c7 bytes_l11c1c7) (entryMap (live .l11c1c7))
      3 0x11c1c7 bytes_l11c1c7 b_l11c1c7 := by
  have f0 : InstrSpec 0x11c1c7 [0x48, 0x8B, 0x77, 0x08] (LoadPre 0x11c1c7 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x11c1c7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c1c7 6 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11c1c7 6 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11c1c7 0x48 (by decide) 6 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c1cb [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x11c1cb) (cmpR64R64Effect 0x11c1cb 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c1cb 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x11c1cb 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1cb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1ce) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x11c1ce 4 0xe8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c1c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c1c7 :=
  Rest.liftedBlock (rest_l11c1c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c1c7 x hx)

theorem rest_l11c1d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c1d4 bytes_l11c1d4) (entryMap (live .l11c1d4))
      3 0x11c1d4 bytes_l11c1d4 b_l11c1d4 := by
  have f0 : InstrSpec 0x11c1d4 [0x48, 0x29, 0xCE] (fun s => s.RIP = 0x11c1d4) (subR64R64Effect 0x11c1d4 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11c1d4 6 1).toInstrSpec (sub_r64_r64_effect_step 0x11c1d4 0x48 0xce (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c1d7 [0x48, 0x81, 0xFE, 0xA0, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x11c1d7) (cmpR64Imm32Effect 0x11c1d7 6 0x9a0)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x11c1d7 6 0x9a0).toInstrSpec (cmp_r64_imm32_effect_step 0x11c1d7 0x48 0xfe 0x9a0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1d7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1de) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x11c1de 5 0x7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c1d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c1d4 :=
  Rest.liftedBlock (rest_l11c1d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c1d4 x hx)

theorem rest_l11c1e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c1e0 bytes_l11c1e0) (entryMap (live .l11c1e0))
      2 0x11c1e0 bytes_l11c1e0 b_l11c1e0 := by
  have f0 : InstrSpec 0x11c1e0 [0x31, 0xF6] (fun s => s.RIP = 0x11c1e0) (xorR32R32Effect 0x11c1e0 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c1e0 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x11c1e0 0xf6 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1e2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x11c1e2 0xad (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c1e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c1e0 :=
  Rest.liftedBlock (rest_l11c1e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c1e0 x hx)

theorem rest_l11c1e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c1e7 bytes_l11c1e7) (entryMap (live .l11c1e7))
      8 0x11c1e7 bytes_l11c1e7 b_l11c1e7 := by
  have f0 : InstrSpec 0x11c1e7 [0x48, 0xC1, 0xEE, 0x05] (fun s => s.RIP = 0x11c1e7) (shrR64Effect 0x11c1e7 4 6 5)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11c1e7 4 6 5).toInstrSpec (shr_r64_imm8_effect_step 0x11c1e7 0x48 0xee 0x5 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c1eb [0x49, 0xB8, 0x85, 0x38, 0x2B, 0x3F, 0x21, 0xCE, 0xCA, 0x4F] (fun s => s.RIP = 0x11c1eb) (movR64Imm64Effect 0x11c1eb 8 0x4fcace213f2b3885)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x11c1eb 8 0x4fcace213f2b3885).toInstrSpec (mov_r64_imm64_effect_step 0x11c1eb 0x49 0xb8 (by decide) (by decide) 0x4fcace213f2b3885) pre_rip
  have f2 : InstrSpec 0x11c1f5 [0x4C, 0x0F, 0xAF, 0xC6] (fun s => s.RIP = 0x11c1f5) (imulR64R64Effect 0x11c1f5 4 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x11c1f5 4 8 6).toInstrSpec (imul_r64_r64_effect_step 0x11c1f5 0x4c (by decide) 0xc6 (by decide)) pre_rip
  have f3 : InstrSpec 0x11c1f9 [0x49, 0xB9, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x1F, 0x00] (fun s => s.RIP = 0x11c1f9) (movR64Imm64Effect 0x11c1f9 9 0x1ffffffffffffe)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x11c1f9 9 0x1ffffffffffffe).toInstrSpec (mov_r64_imm64_effect_step 0x11c1f9 0x49 0xb9 (by decide) (by decide) 0x1ffffffffffffe) pre_rip
  have f4 : InstrSpec 0x11c203 [0x4D, 0x21, 0xC1] (fun s => s.RIP = 0x11c203) (andR64R64Effect 0x11c203 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11c203 9 8).toInstrSpec (and_r64_r64_effect_step 0x11c203 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c206 [0x4C, 0x8D, 0x91, 0x30, 0x12, 0x00, 0x00] (fun s => s.RIP = 0x11c206) (leaR64Effect 0x11c206 10 (.base 1 (.d32 0x1230)))
      [.gpr 1] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x11c206 10 (.base 1 (.d32 0x1230))).toInstrSpec (lea_r64_effect_step 0x11c206 0x4c (by decide) 2 (.base 1 (.d32 0x1230)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c20d [0x31, 0xF6] (fun s => s.RIP = 0x11c20d) (xorR32R32Effect 0x11c20d 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c20d 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x11c20d 0xf6 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1eb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1f5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c1f9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 57), (9, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c203) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 57), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c206) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 57), (9, 61), (10, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c20d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 65), (7, 7), (8, 57), (9, 61), (10, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c20f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 67) (jmp_rel8_effect_step 0x11c20f 0x1f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c1e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c1e7 :=
  Rest.liftedBlock (rest_l11c1e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c1e7 x hx)

theorem rest_l11c220 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c220 bytes_l11c220) (entryMap (live .l11c220))
      4 0x11c220 bytes_l11c220 b_l11c220 := by
  have f0 : InstrSpec 0x11c220 [0x48, 0x83, 0xC6, 0x02] (fun s => s.RIP = 0x11c220) (addR64Imm8Effect 0x11c220 6 0x2)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11c220 6 0x2).toInstrSpec (add_r64_imm8_effect_step 0x11c220 0x48 0xc6 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c224 [0x49, 0x81, 0xC2, 0x40, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x11c224) (addR64Imm32Effect 0x11c224 10 0x1340)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11c224 10 0x1340).toInstrSpec (add_r64_imm32_effect_step 0x11c224 0x49 0xc2 0x1340 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c22b [0x49, 0x39, 0xF1] (fun s => s.RIP = 0x11c22b) (cmpR64R64Effect 0x11c22b 9 6)
      [.gpr 9, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c22b 9 6).toInstrSpec (cmp_r64_r64_effect_step 0x11c22b 0x49 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c224) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c22b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c22e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x11c22e 4 0x5e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c220 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c220 :=
  Rest.liftedBlock (rest_l11c220 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c220 x hx)

theorem rest_l11c230 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c230 bytes_l11c230) (entryMap (live .l11c230))
      3 0x11c230 bytes_l11c230 b_l11c230 := by
  have f0 : InstrSpec 0x11c230 [0x4D, 0x8B, 0x9A, 0x50, 0xF5, 0xFF, 0xFF] (LoadPre 0x11c230 (fun s => AddrMode.addr (.base 10 (.d32 0xfffff550)) s (0x11c230 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c230 11 (.base 10 (.d32 0xfffff550)))
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11c230 11 (.base 10 (.d32 0xfffff550))).toInstrSpec (mov_r64_m64_effect_step 0x11c230 0x4d (by decide) 3 (.base 10 (.d32 0xfffff550)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c237 [0x4C, 0x39, 0xD8] (fun s => s.RIP = 0x11c237) (cmpR64R64Effect 0x11c237 0 11)
      [.gpr 0, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c237 0 11).toInstrSpec (cmp_r64_r64_effect_step 0x11c237 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c237) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c23a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c23a 6 0x24) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c230 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c230 :=
  Rest.liftedBlock (rest_l11c230 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c230 x hx)

theorem rest_l11c23c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c23c bytes_l11c23c) (entryMap (live .l11c23c))
      3 0x11c23c bytes_l11c23c b_l11c23c := by
  have f0 : InstrSpec 0x11c23c [0x4D, 0x8B, 0x9A, 0x60, 0xF6, 0xFF, 0xFF] (LoadPre 0x11c23c (fun s => AddrMode.addr (.base 10 (.d32 0xfffff660)) s (0x11c23c + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c23c 11 (.base 10 (.d32 0xfffff660)))
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11c23c 11 (.base 10 (.d32 0xfffff660))).toInstrSpec (mov_r64_m64_effect_step 0x11c23c 0x4d (by decide) 3 (.base 10 (.d32 0xfffff660)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c243 [0x4C, 0x39, 0xD8] (fun s => s.RIP = 0x11c243) (cmpR64R64Effect 0x11c243 0 11)
      [.gpr 0, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c243 0 11).toInstrSpec (cmp_r64_r64_effect_step 0x11c243 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c243) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c246) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c246 6 0x27) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c23c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c23c :=
  Rest.liftedBlock (rest_l11c23c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c23c x hx)

theorem rest_l11c248 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c248 bytes_l11c248) (entryMap (live .l11c248))
      3 0x11c248 bytes_l11c248 b_l11c248 := by
  have f0 : InstrSpec 0x11c248 [0x4D, 0x8B, 0x9A, 0xF0, 0xFE, 0xFF, 0xFF] (LoadPre 0x11c248 (fun s => AddrMode.addr (.base 10 (.d32 0xfffffef0)) s (0x11c248 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c248 11 (.base 10 (.d32 0xfffffef0)))
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11c248 11 (.base 10 (.d32 0xfffffef0))).toInstrSpec (mov_r64_m64_effect_step 0x11c248 0x4d (by decide) 3 (.base 10 (.d32 0xfffffef0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c24f [0x4C, 0x39, 0xD8] (fun s => s.RIP = 0x11c24f) (cmpR64R64Effect 0x11c24f 0 11)
      [.gpr 0, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c24f 0 11).toInstrSpec (cmp_r64_r64_effect_step 0x11c24f 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c24f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c252) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c252 6 0x2a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c248 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c248 :=
  Rest.liftedBlock (rest_l11c248 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c248 x hx)

theorem rest_l11c254 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c254 bytes_l11c254) (entryMap (live .l11c254))
      3 0x11c254 bytes_l11c254 b_l11c254 := by
  have f0 : InstrSpec 0x11c254 [0x4D, 0x8B, 0x1A] (LoadPre 0x11c254 (fun s => AddrMode.addr (.base 10 .none) s (0x11c254 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c254 11 (.base 10 .none))
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11c254 11 (.base 10 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c254 0x4d (by decide) 3 (.base 10 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c257 [0x4C, 0x39, 0xD8] (fun s => s.RIP = 0x11c257) (cmpR64R64Effect 0x11c257 0 11)
      [.gpr 0, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c257 0 11).toInstrSpec (cmp_r64_r64_effect_step 0x11c257 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c257) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c25a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c25a 7 0xc4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c254 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c254 :=
  Rest.liftedBlock (rest_l11c254 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c254 x hx)

theorem rest_l11c25c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c25c bytes_l11c25c) (entryMap (live .l11c25c))
      1 0x11c25c bytes_l11c25c b_l11c25c := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x11c25c 0x2b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c25c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c25c :=
  Rest.liftedBlock (rest_l11c25c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c25c x hx)

theorem rest_l11c260 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c260 bytes_l11c260) (entryMap (live .l11c260))
      4 0x11c260 bytes_l11c260 b_l11c260 := by
  have f0 : InstrSpec 0x11c260 [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x11c260) (movR64R64Effect 0x11c260 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c260 0 11).toInstrSpec (mov_r64_r64_effect_step 0x11c260 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c263 [0x4D, 0x8B, 0x9A, 0x60, 0xF6, 0xFF, 0xFF] (LoadPre 0x11c263 (fun s => AddrMode.addr (.base 10 (.d32 0xfffff660)) s (0x11c263 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c263 11 (.base 10 (.d32 0xfffff660)))
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11c263 11 (.base 10 (.d32 0xfffff660))).toInstrSpec (mov_r64_m64_effect_step 0x11c263 0x4d (by decide) 3 (.base 10 (.d32 0xfffff660)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c26a [0x4C, 0x39, 0xD8] (fun s => s.RIP = 0x11c26a) (cmpR64R64Effect 0x11c26a 0 11)
      [.gpr 0, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c26a 0 11).toInstrSpec (cmp_r64_r64_effect_step 0x11c26a 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c263) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c26a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c26d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x11c26d 7 0xd9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c260 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c260 :=
  Rest.liftedBlock (rest_l11c260 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c260 x hx)

theorem rest_l11c26f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c26f bytes_l11c26f) (entryMap (live .l11c26f))
      4 0x11c26f bytes_l11c26f b_l11c26f := by
  have f0 : InstrSpec 0x11c26f [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x11c26f) (movR64R64Effect 0x11c26f 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c26f 0 11).toInstrSpec (mov_r64_r64_effect_step 0x11c26f 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c272 [0x4D, 0x8B, 0x9A, 0xF0, 0xFE, 0xFF, 0xFF] (LoadPre 0x11c272 (fun s => AddrMode.addr (.base 10 (.d32 0xfffffef0)) s (0x11c272 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c272 11 (.base 10 (.d32 0xfffffef0)))
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11c272 11 (.base 10 (.d32 0xfffffef0))).toInstrSpec (mov_r64_m64_effect_step 0x11c272 0x4d (by decide) 3 (.base 10 (.d32 0xfffffef0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c279 [0x4C, 0x39, 0xD8] (fun s => s.RIP = 0x11c279) (cmpR64R64Effect 0x11c279 0 11)
      [.gpr 0, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c279 0 11).toInstrSpec (cmp_r64_r64_effect_step 0x11c279 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c272) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c279) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c27c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x11c27c 7 0xd6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c26f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c26f :=
  Rest.liftedBlock (rest_l11c26f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c26f x hx)

theorem rest_l11c27e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c27e bytes_l11c27e) (entryMap (live .l11c27e))
      4 0x11c27e bytes_l11c27e b_l11c27e := by
  have f0 : InstrSpec 0x11c27e [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x11c27e) (movR64R64Effect 0x11c27e 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c27e 0 11).toInstrSpec (mov_r64_r64_effect_step 0x11c27e 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c281 [0x4D, 0x8B, 0x1A] (LoadPre 0x11c281 (fun s => AddrMode.addr (.base 10 .none) s (0x11c281 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c281 11 (.base 10 .none))
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11c281 11 (.base 10 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c281 0x4d (by decide) 3 (.base 10 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c284 [0x4C, 0x39, 0xD8] (fun s => s.RIP = 0x11c284) (cmpR64R64Effect 0x11c284 0 11)
      [.gpr 0, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c284 0 11).toInstrSpec (cmp_r64_r64_effect_step 0x11c284 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c281) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c284) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c287) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x11c287 7 0x97) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c27e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c27e :=
  Rest.liftedBlock (rest_l11c27e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c27e x hx)

theorem rest_l11c289 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c289 bytes_l11c289) (entryMap (live .l11c289))
      2 0x11c289 bytes_l11c289 b_l11c289 := by
  have f0 : InstrSpec 0x11c289 [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x11c289) (movR64R64Effect 0x11c289 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c289 0 11).toInstrSpec (mov_r64_r64_effect_step 0x11c289 0x4c 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c28c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x11c28c 0x92 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c289 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c289 :=
  Rest.liftedBlock (rest_l11c289 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c289 x hx)

theorem rest_l11c28e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c28e bytes_l11c28e) (entryMap (live .l11c28e))
      2 0x11c28e bytes_l11c28e b_l11c28e := by
  have f0 : InstrSpec 0x11c28e [0x41, 0xF6, 0xC0, 0x01] (fun s => s.RIP = 0x11c28e) (testR8Imm8Effect 0x11c28e 8 0x1)
      [.gpr 8] [] [.flags, .rip] :=
    (testR8Imm8Effect_footprint 0x11c28e 8 0x1).toInstrSpec (test_r8_imm8_effect_step 0x11c28e 0x41 0xc0 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c292) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x11c292 4 0x28) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c28e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c28e :=
  Rest.liftedBlock (rest_l11c28e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c28e x hx)

theorem rest_l11c294 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c294 bytes_l11c294) (entryMap (live .l11c294))
      8 0x11c294 bytes_l11c294 b_l11c294 := by
  have f0 : InstrSpec 0x11c294 [0x48, 0x69, 0xF6, 0xA0, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x11c294) (imulR64R64Imm32Effect 0x11c294 7 6 6 0x9a0)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x11c294 7 6 6 0x9a0).toInstrSpec (imul_r64_r64_imm32_effect_step 0x11c294 0x48 (by decide) 0xf6 (by decide) 0x9a0) pre_rip
  have f1 : InstrSpec 0x11c29b [0x4C, 0x8B, 0x84, 0x31, 0x80, 0x07, 0x00, 0x00] (LoadPre 0x11c29b (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d32 0x780)) s (0x11c29b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c29b 8 (.sib 1 (some 6) 0 (.d32 0x780)))
      [.gpr 1, .gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11c29b 8 (.sib 1 (some 6) 0 (.d32 0x780))).toInstrSpec (mov_r64_m64_effect_step 0x11c29b 0x4c (by decide) 0 (.sib 1 (some 6) 0 (.d32 0x780)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c2a3 [0x48, 0x8B, 0x8C, 0x31, 0x90, 0x08, 0x00, 0x00] (LoadPre 0x11c2a3 (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d32 0x890)) s (0x11c2a3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x11c2a3 1 (.sib 1 (some 6) 0 (.d32 0x890)))
      [.gpr 1, .gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c2a3 1 (.sib 1 (some 6) 0 (.d32 0x890))).toInstrSpec (mov_r64_m64_effect_step 0x11c2a3 0x48 (by decide) 1 (.sib 1 (some 6) 0 (.d32 0x890)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11c2ab [0x4C, 0x39, 0xC0] (fun s => s.RIP = 0x11c2ab) (cmpR64R64Effect 0x11c2ab 0 8)
      [.gpr 0, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c2ab 0 8).toInstrSpec (cmp_r64_r64_effect_step 0x11c2ab 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c2ae [0x4C, 0x0F, 0x47, 0xC0] (fun s => s.RIP = 0x11c2ae) (atFlags (condHolds 7) (cmovR64R64Effect 0x11c2ae 4 8 0))
      [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x11c2ae 4 8 0 7).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11c2ae 7 0x4c (by decide) 0xc0 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x11c2b2 [0x49, 0x39, 0xC8] (fun s => s.RIP = 0x11c2b2) (cmpR64R64Effect 0x11c2b2 8 1)
      [.gpr 8, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c2b2 8 1).toInstrSpec (cmp_r64_r64_effect_step 0x11c2b2 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11c2b5 [0x4C, 0x0F, 0x46, 0xC1] (fun s => s.RIP = 0x11c2b5) (atFlags (condHolds 6) (cmovR64R64Effect 0x11c2b5 4 8 1))
      [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x11c2b5 4 8 1 6).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11c2b5 6 0x4c (by decide) 0xc1 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11c2b9 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x11c2b9) (movR64R64Effect 0x11c2b9 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c2b9 0 8).toInstrSpec (mov_r64_r64_effect_step 0x11c2b9 0x4c 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c29b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2ae) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2b2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 62), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2b5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2b9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 57), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (8, 67), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2bc) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l11c294 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c294 :=
  Rest.liftedBlock (rest_l11c294 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c294 x hx)

theorem rest_l11c2bc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c2bc bytes_l11c2bc) (entryMap (live .l11c2bc))
      2 0x11c2bc bytes_l11c2bc b_l11c2bc := by
  have f0 : InstrSpec 0x11c2bc [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x11c2bc) (testR64R64Effect 0x11c2bc 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11c2bc 2 2).toInstrSpec (test_r64_r64_effect_step 0x11c2bc 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2bf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x11c2bf 4 0xf5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c2bc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c2bc :=
  Rest.liftedBlock (rest_l11c2bc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c2bc x hx)

theorem rest_l11c2c5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c2c5 bytes_l11c2c5) (entryMap (live .l11c2c5))
      5 0x11c2c5 bytes_l11c2c5 b_l11c2c5 := by
  have f0 : InstrSpec 0x11c2c5 [0x4C, 0x8B, 0x4F, 0x60] (LoadPre 0x11c2c5 (fun s => AddrMode.addr (.base 7 (.d8 0x60)) s (0x11c2c5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c2c5 9 (.base 7 (.d8 0x60)))
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x11c2c5 9 (.base 7 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x11c2c5 0x4c (by decide) 1 (.base 7 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c2c9 [0x4C, 0x8B, 0x57, 0x68] (LoadPre 0x11c2c9 (fun s => AddrMode.addr (.base 7 (.d8 0x68)) s (0x11c2c9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c2c9 10 (.base 7 (.d8 0x68)))
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11c2c9 10 (.base 7 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x11c2c9 0x4c (by decide) 2 (.base 7 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c2cd [0x4D, 0x89, 0xD0] (fun s => s.RIP = 0x11c2cd) (movR64R64Effect 0x11c2cd 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11c2cd 8 10).toInstrSpec (mov_r64_r64_effect_step 0x11c2cd 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c2d0 [0x4D, 0x29, 0xC8] (fun s => s.RIP = 0x11c2d0) (subR64R64Effect 0x11c2d0 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11c2d0 8 9).toInstrSpec (sub_r64_r64_effect_step 0x11c2d0 0x4d 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2cd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2d0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2d3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel32_effect_step 0x11c2d3 4 0xe1) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c2c5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c2c5 :=
  Rest.liftedBlock (rest_l11c2c5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c2c5 x hx)

theorem rest_l11c2d9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c2d9 bytes_l11c2d9) (entryMap (live .l11c2d9))
      7 0x11c2d9 bytes_l11c2d9 b_l11c2d9 := by
  have f0 : InstrSpec 0x11c2d9 [0x48, 0x8B, 0x4F, 0x50] (LoadPre 0x11c2d9 (fun s => AddrMode.addr (.base 7 (.d8 0x50)) s (0x11c2d9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c2d9 1 (.base 7 (.d8 0x50)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11c2d9 1 (.base 7 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x11c2d9 0x48 (by decide) 1 (.base 7 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c2dd [0x49, 0x69, 0xF1, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c2dd) (imulR64R64Imm32Effect 0x11c2dd 7 6 9 0x110)
      [.gpr 9] [] [.reg 6, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x11c2dd 7 6 9 0x110).toInstrSpec (imul_r64_r64_imm32_effect_step 0x11c2dd 0x49 (by decide) 0xf1 (by decide) 0x110) pre_rip
  have f2 : InstrSpec 0x11c2e4 [0x44, 0x89, 0xC2] (fun s => s.RIP = 0x11c2e4) (movR32R32Effect 0x11c2e4 3 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x11c2e4 3 2 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x11c2e4 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c2e7 [0x83, 0xE2, 0x03] (fun s => s.RIP = 0x11c2e7) (andR32Imm8Effect 0x11c2e7 3 2 0x3)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x11c2e7 3 2 0x3).toInstrSpec (and_r32_imm8_effect_step 0x11c2e7 0xe2 0x3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11c2ea [0x4D, 0x29, 0xD1] (fun s => s.RIP = 0x11c2ea) (subR64R64Effect 0x11c2ea 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11c2ea 9 10).toInstrSpec (sub_r64_r64_effect_step 0x11c2ea 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c2ed [0x49, 0x83, 0xF9, 0xFC] (fun s => s.RIP = 0x11c2ed) (cmpR64Imm8Effect 0x11c2ed 9 0xfc)
      [.gpr 9] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x11c2ed 9 0xfc).toInstrSpec (cmp_r64_imm8_effect_step 0x11c2ed 0x49 0xf9 0xfc (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2e4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 57), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2e7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 59), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2ea) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 59), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2ed) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 59), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2f1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x11c2f1 6 0x7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c2d9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c2d9 :=
  Rest.liftedBlock (rest_l11c2d9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c2d9 x hx)

theorem rest_l11c2f3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c2f3 bytes_l11c2f3) (entryMap (live .l11c2f3))
      2 0x11c2f3 bytes_l11c2f3 b_l11c2f3 := by
  have f0 : InstrSpec 0x11c2f3 [0x31, 0xFF] (fun s => s.RIP = 0x11c2f3) (xorR32R32Effect 0x11c2f3 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c2f3 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c2f3 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x11c2f5 0x8d (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c2f3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c2f3 :=
  Rest.liftedBlock (rest_l11c2f3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c2f3 x hx)

theorem rest_l11c2fa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c2fa bytes_l11c2fa) (entryMap (live .l11c2fa))
      4 0x11c2fa bytes_l11c2fa b_l11c2fa := by
  have f0 : InstrSpec 0x11c2fa [0x4C, 0x8D, 0x0C, 0x31] (fun s => s.RIP = 0x11c2fa) (leaR64Effect 0x11c2fa 9 (.sib 1 (some 6) 0 .none))
      [.gpr 1, .gpr 6] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x11c2fa 9 (.sib 1 (some 6) 0 .none)).toInstrSpec (lea_r64_effect_step 0x11c2fa 0x4c (by decide) 1 (.sib 1 (some 6) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c2fe [0x49, 0x83, 0xE0, 0xFC] (fun s => s.RIP = 0x11c2fe) (andR64Imm8Effect 0x11c2fe 8 0xfc)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x11c2fe 8 0xfc).toInstrSpec (and_r64_imm8_effect_step 0x11c2fe 0x49 0xe0 0xfc (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c302 [0x31, 0xFF] (fun s => s.RIP = 0x11c302) (xorR32R32Effect 0x11c302 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c302 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x11c302 0xff (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c2fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c302) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 55), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c304) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x11c304 0x1a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c2fa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c2fa :=
  Rest.liftedBlock (rest_l11c2fa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c2fa x hx)

theorem rest_l11c310 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c310 bytes_l11c310) (entryMap (live .l11c310))
      4 0x11c310 bytes_l11c310 b_l11c310 := by
  have f0 : InstrSpec 0x11c310 [0x48, 0x83, 0xC7, 0x04] (fun s => s.RIP = 0x11c310) (addR64Imm8Effect 0x11c310 7 0x4)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11c310 7 0x4).toInstrSpec (add_r64_imm8_effect_step 0x11c310 0x48 0xc7 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c314 [0x49, 0x81, 0xC1, 0x40, 0x04, 0x00, 0x00] (fun s => s.RIP = 0x11c314) (addR64Imm32Effect 0x11c314 9 0x440)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11c314 9 0x440).toInstrSpec (add_r64_imm32_effect_step 0x11c314 0x49 0xc1 0x440 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c31b [0x49, 0x39, 0xF8] (fun s => s.RIP = 0x11c31b) (cmpR64R64Effect 0x11c31b 8 7)
      [.gpr 8, .gpr 7] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c31b 8 7).toInstrSpec (cmp_r64_r64_effect_step 0x11c31b 0x49 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c314) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c31b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c31e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x11c31e 4 0x62) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c310 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c310 :=
  Rest.liftedBlock (rest_l11c310 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c310 x hx)

theorem rest_l11c320 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c320 bytes_l11c320) (entryMap (live .l11c320))
      3 0x11c320 bytes_l11c320 b_l11c320 := by
  have f0 : InstrSpec 0x11c320 [0x4D, 0x8B, 0x11] (LoadPre 0x11c320 (fun s => AddrMode.addr (.base 9 .none) s (0x11c320 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11c320 10 (.base 9 .none))
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11c320 10 (.base 9 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c320 0x4d (by decide) 2 (.base 9 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c323 [0x4C, 0x39, 0xD0] (fun s => s.RIP = 0x11c323) (cmpR64R64Effect 0x11c323 0 10)
      [.gpr 0, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c323 0 10).toInstrSpec (cmp_r64_r64_effect_step 0x11c323 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c323) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c326) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c326 6 0x28) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c320 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c320 :=
  Rest.liftedBlock (rest_l11c320 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c320 x hx)

theorem rest_l11c328 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c328 bytes_l11c328) (entryMap (live .l11c328))
      3 0x11c328 bytes_l11c328 b_l11c328 := by
  have f0 : InstrSpec 0x11c328 [0x4D, 0x8B, 0x91, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x11c328 (fun s => AddrMode.addr (.base 9 (.d32 0x110)) s (0x11c328 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c328 10 (.base 9 (.d32 0x110)))
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11c328 10 (.base 9 (.d32 0x110))).toInstrSpec (mov_r64_m64_effect_step 0x11c328 0x4d (by decide) 2 (.base 9 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c32f [0x4C, 0x39, 0xD0] (fun s => s.RIP = 0x11c32f) (cmpR64R64Effect 0x11c32f 0 10)
      [.gpr 0, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c32f 0 10).toInstrSpec (cmp_r64_r64_effect_step 0x11c32f 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c32f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c332) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c332 6 0x2b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c328 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c328 :=
  Rest.liftedBlock (rest_l11c328 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c328 x hx)

theorem rest_l11c334 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c334 bytes_l11c334) (entryMap (live .l11c334))
      3 0x11c334 bytes_l11c334 b_l11c334 := by
  have f0 : InstrSpec 0x11c334 [0x4D, 0x8B, 0x91, 0x20, 0x02, 0x00, 0x00] (LoadPre 0x11c334 (fun s => AddrMode.addr (.base 9 (.d32 0x220)) s (0x11c334 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c334 10 (.base 9 (.d32 0x220)))
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11c334 10 (.base 9 (.d32 0x220))).toInstrSpec (mov_r64_m64_effect_step 0x11c334 0x4d (by decide) 2 (.base 9 (.d32 0x220)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c33b [0x4C, 0x39, 0xD0] (fun s => s.RIP = 0x11c33b) (cmpR64R64Effect 0x11c33b 0 10)
      [.gpr 0, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c33b 0 10).toInstrSpec (cmp_r64_r64_effect_step 0x11c33b 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c33b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c33e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c33e 6 0x2e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c334 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c334 :=
  Rest.liftedBlock (rest_l11c334 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c334 x hx)

theorem rest_l11c340 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c340 bytes_l11c340) (entryMap (live .l11c340))
      3 0x11c340 bytes_l11c340 b_l11c340 := by
  have f0 : InstrSpec 0x11c340 [0x4D, 0x8B, 0x91, 0x30, 0x03, 0x00, 0x00] (LoadPre 0x11c340 (fun s => AddrMode.addr (.base 9 (.d32 0x330)) s (0x11c340 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c340 10 (.base 9 (.d32 0x330)))
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11c340 10 (.base 9 (.d32 0x330))).toInstrSpec (mov_r64_m64_effect_step 0x11c340 0x4d (by decide) 2 (.base 9 (.d32 0x330)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11c347 [0x4C, 0x39, 0xD0] (fun s => s.RIP = 0x11c347) (cmpR64R64Effect 0x11c347 0 10)
      [.gpr 0, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c347 0 10).toInstrSpec (cmp_r64_r64_effect_step 0x11c347 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c347) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c34a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x11c34a 7 0xc4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c340 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c340 :=
  Rest.liftedBlock (rest_l11c340 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c340 x hx)

theorem rest_l11c34c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c34c bytes_l11c34c) (entryMap (live .l11c34c))
      1 0x11c34c bytes_l11c34c b_l11c34c := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x11c34c 0x2f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c34c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c34c :=
  Rest.liftedBlock (rest_l11c34c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c34c x hx)

theorem rest_l11c350 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c350 bytes_l11c350) (entryMap (live .l11c350))
      4 0x11c350 bytes_l11c350 b_l11c350 := by
  have f0 : InstrSpec 0x11c350 [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x11c350) (movR64R64Effect 0x11c350 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c350 0 10).toInstrSpec (mov_r64_r64_effect_step 0x11c350 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c353 [0x4D, 0x8B, 0x91, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x11c353 (fun s => AddrMode.addr (.base 9 (.d32 0x110)) s (0x11c353 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c353 10 (.base 9 (.d32 0x110)))
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11c353 10 (.base 9 (.d32 0x110))).toInstrSpec (mov_r64_m64_effect_step 0x11c353 0x4d (by decide) 2 (.base 9 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c35a [0x4C, 0x39, 0xD0] (fun s => s.RIP = 0x11c35a) (cmpR64R64Effect 0x11c35a 0 10)
      [.gpr 0, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c35a 0 10).toInstrSpec (cmp_r64_r64_effect_step 0x11c35a 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c353) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c35a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c35d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x11c35d 7 0xd5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c350 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c350 :=
  Rest.liftedBlock (rest_l11c350 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c350 x hx)

theorem rest_l11c35f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c35f bytes_l11c35f) (entryMap (live .l11c35f))
      4 0x11c35f bytes_l11c35f b_l11c35f := by
  have f0 : InstrSpec 0x11c35f [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x11c35f) (movR64R64Effect 0x11c35f 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c35f 0 10).toInstrSpec (mov_r64_r64_effect_step 0x11c35f 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c362 [0x4D, 0x8B, 0x91, 0x20, 0x02, 0x00, 0x00] (LoadPre 0x11c362 (fun s => AddrMode.addr (.base 9 (.d32 0x220)) s (0x11c362 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c362 10 (.base 9 (.d32 0x220)))
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11c362 10 (.base 9 (.d32 0x220))).toInstrSpec (mov_r64_m64_effect_step 0x11c362 0x4d (by decide) 2 (.base 9 (.d32 0x220)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c369 [0x4C, 0x39, 0xD0] (fun s => s.RIP = 0x11c369) (cmpR64R64Effect 0x11c369 0 10)
      [.gpr 0, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c369 0 10).toInstrSpec (cmp_r64_r64_effect_step 0x11c369 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c362) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c369) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c36c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x11c36c 7 0xd2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c35f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c35f :=
  Rest.liftedBlock (rest_l11c35f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c35f x hx)

theorem rest_l11c36e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c36e bytes_l11c36e) (entryMap (live .l11c36e))
      4 0x11c36e bytes_l11c36e b_l11c36e := by
  have f0 : InstrSpec 0x11c36e [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x11c36e) (movR64R64Effect 0x11c36e 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c36e 0 10).toInstrSpec (mov_r64_r64_effect_step 0x11c36e 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c371 [0x4D, 0x8B, 0x91, 0x30, 0x03, 0x00, 0x00] (LoadPre 0x11c371 (fun s => AddrMode.addr (.base 9 (.d32 0x330)) s (0x11c371 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x11c371 10 (.base 9 (.d32 0x330)))
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11c371 10 (.base 9 (.d32 0x330))).toInstrSpec (mov_r64_m64_effect_step 0x11c371 0x4d (by decide) 2 (.base 9 (.d32 0x330)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c378 [0x4C, 0x39, 0xD0] (fun s => s.RIP = 0x11c378) (cmpR64R64Effect 0x11c378 0 10)
      [.gpr 0, .gpr 10] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c378 0 10).toInstrSpec (cmp_r64_r64_effect_step 0x11c378 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c371) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c378) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c37b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x11c37b 7 0x93) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c36e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c36e :=
  Rest.liftedBlock (rest_l11c36e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c36e x hx)

theorem rest_l11c37d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c37d bytes_l11c37d) (entryMap (live .l11c37d))
      2 0x11c37d bytes_l11c37d b_l11c37d := by
  have f0 : InstrSpec 0x11c37d [0x4C, 0x89, 0xD0] (fun s => s.RIP = 0x11c37d) (movR64R64Effect 0x11c37d 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11c37d 0 10).toInstrSpec (mov_r64_r64_effect_step 0x11c37d 0x4c 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c380) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x11c380 0x8e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l11c37d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c37d :=
  Rest.liftedBlock (rest_l11c37d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c37d x hx)

theorem rest_l11c382 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c382 bytes_l11c382) (entryMap (live .l11c382))
      2 0x11c382 bytes_l11c382 b_l11c382 := by
  have f0 : InstrSpec 0x11c382 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x11c382) (testR64R64Effect 0x11c382 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x11c382 2 2).toInstrSpec (test_r64_r64_effect_step 0x11c382 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c385) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x11c385 4 0x33) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c382 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c382 :=
  Rest.liftedBlock (rest_l11c382 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c382 x hx)

theorem rest_l11c387 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c387 bytes_l11c387) (entryMap (live .l11c387))
      6 0x11c387 bytes_l11c387 b_l11c387 := by
  have f0 : InstrSpec 0x11c387 [0x48, 0x69, 0xFF, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c387) (imulR64R64Imm32Effect 0x11c387 7 7 7 0x110)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x11c387 7 7 7 0x110).toInstrSpec (imul_r64_r64_imm32_effect_step 0x11c387 0x48 (by decide) 0xff (by decide) 0x110) pre_rip
  have f1 : InstrSpec 0x11c38e [0x48, 0x01, 0xF7] (fun s => s.RIP = 0x11c38e) (addR64R64Effect 0x11c38e 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c38e 7 6).toInstrSpec (add_r64_r64_effect_step 0x11c38e 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11c391 [0x48, 0x01, 0xF9] (fun s => s.RIP = 0x11c391) (addR64R64Effect 0x11c391 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11c391 1 7).toInstrSpec (add_r64_r64_effect_step 0x11c391 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c394 [0x48, 0x69, 0xD2, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c394) (imulR64R64Imm32Effect 0x11c394 7 2 2 0x110)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (imulR64R64Imm32Effect_footprint 0x11c394 7 2 2 0x110).toInstrSpec (imul_r64_r64_imm32_effect_step 0x11c394 0x48 (by decide) 0xd2 (by decide) 0x110) pre_rip
  have f4 : InstrSpec 0x11c39b [0x31, 0xF6] (fun s => s.RIP = 0x11c39b) (xorR32R32Effect 0x11c39b 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11c39b 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x11c39b 0xf6 (by decide)) pre_rip
  have f5 : InstrSpec 0x11c39d [0x0F, 0x1F, 0x00] (fun s => s.RIP = 0x11c39d) (fun _ => nopEffect 0x11c39d 3)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11c39d 3).toInstrSpec (nop_m_effect_step 0x11c39d [] (by decide) (by decide) (.base 0 .none) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c38e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c391) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c394) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 59), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c39b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 57), (2, 59), (4, 4), (5, 5), (6, 61), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c39d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 57), (2, 59), (4, 4), (5, 5), (6, 61), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3a0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 64) (by decide) rfl

theorem block_l11c387 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c387 :=
  Rest.liftedBlock (rest_l11c387 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c387 x hx)

theorem rest_l11c3a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c3a0 bytes_l11c3a0) (entryMap (live .l11c3a0))
      7 0x11c3a0 bytes_l11c3a0 b_l11c3a0 := by
  have f0 : InstrSpec 0x11c3a0 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11c3a0) (movR64R64Effect 0x11c3a0 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11c3a0 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11c3a0 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11c3a3 [0x48, 0x8B, 0x04, 0x31] (LoadPre 0x11c3a3 (fun s => AddrMode.addr (.sib 1 (some 6) 0 .none) s (0x11c3a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11c3a3 0 (.sib 1 (some 6) 0 .none))
      [.gpr 1, .gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11c3a3 0 (.sib 1 (some 6) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11c3a3 0x48 (by decide) 0 (.sib 1 (some 6) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11c3a7 [0x48, 0x39, 0xC7] (fun s => s.RIP = 0x11c3a7) (cmpR64R64Effect 0x11c3a7 7 0)
      [.gpr 7, .gpr 0] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c3a7 7 0).toInstrSpec (cmp_r64_r64_effect_step 0x11c3a7 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11c3aa [0x48, 0x0F, 0x47, 0xC7] (fun s => s.RIP = 0x11c3aa) (atFlags (condHolds 7) (cmovR64R64Effect 0x11c3aa 4 0 7))
      [.gpr 0, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (cmovR64R64Effect_footprint 0x11c3aa 4 0 7 7).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11c3aa 7 0x48 (by decide) 0xc7 (by decide) c)) pre_rip
  have f4 : InstrSpec 0x11c3ae [0x48, 0x81, 0xC6, 0x10, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x11c3ae) (addR64Imm32Effect 0x11c3ae 6 0x110)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x11c3ae 6 0x110).toInstrSpec (add_r64_imm32_effect_step 0x11c3ae 0x48 0xc6 0x110 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11c3b5 [0x48, 0x39, 0xF2] (fun s => s.RIP = 0x11c3b5) (cmpR64R64Effect 0x11c3b5 2 6)
      [.gpr 2, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x11c3b5 2 6).toInstrSpec (cmp_r64_r64_effect_step 0x11c3b5 0x48 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3aa) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3ae) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 62), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3b5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 62), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3b8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 66) (jcc_rel8_effect_step 0x11c3b8 5 0xe6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11c3a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c3a0 :=
  Rest.liftedBlock (rest_l11c3a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c3a0 x hx)

theorem rest_l11c3ba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11c3ba bytes_l11c3ba) (entryMap (live .l11c3ba))
      2 0x11c3ba bytes_l11c3ba b_l11c3ba := by
  have f0 : InstrSpec 0x11c3ba [0x5B] (PopPre 0x11c3ba) (popR64Effect 0x11c3ba 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11c3ba 1 3).toInstrSpec (pop_r64_effect_step 0x11c3ba 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x11c3bb [0xC3] (RetPre 0x11c3bb) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11c3bb).toInstrSpec (ret_effect_step 0x11c3bb) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11c3bb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l11c3ba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11c3ba :=
  Rest.liftedBlock (rest_l11c3ba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11c3ba x hx)

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

theorem_by block_l11c0b0_eval :
    program.runBlock (dialect code) ⟨.l11c0b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c0c2_eval :
    program.runBlock (dialect code) ⟨.l11c0c2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c0d6_eval :
    program.runBlock (dialect code) ⟨.l11c0d6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c0f1_eval :
    program.runBlock (dialect code) ⟨.l11c0f1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c0f9_eval :
    program.runBlock (dialect code) ⟨.l11c0f9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c110_eval :
    program.runBlock (dialect code) ⟨.l11c110, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c120_eval :
    program.runBlock (dialect code) ⟨.l11c120, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c128_eval :
    program.runBlock (dialect code) ⟨.l11c128, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c134_eval :
    program.runBlock (dialect code) ⟨.l11c134, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c140_eval :
    program.runBlock (dialect code) ⟨.l11c140, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c14c_eval :
    program.runBlock (dialect code) ⟨.l11c14c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c150_eval :
    program.runBlock (dialect code) ⟨.l11c150, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c15f_eval :
    program.runBlock (dialect code) ⟨.l11c15f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c16e_eval :
    program.runBlock (dialect code) ⟨.l11c16e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c17d_eval :
    program.runBlock (dialect code) ⟨.l11c17d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c182_eval :
    program.runBlock (dialect code) ⟨.l11c182, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c187_eval :
    program.runBlock (dialect code) ⟨.l11c187, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c1a0_eval :
    program.runBlock (dialect code) ⟨.l11c1a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c1ba_eval :
    program.runBlock (dialect code) ⟨.l11c1ba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c1c7_eval :
    program.runBlock (dialect code) ⟨.l11c1c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c1d4_eval :
    program.runBlock (dialect code) ⟨.l11c1d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c1e0_eval :
    program.runBlock (dialect code) ⟨.l11c1e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c1e7_eval :
    program.runBlock (dialect code) ⟨.l11c1e7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c220_eval :
    program.runBlock (dialect code) ⟨.l11c220, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c230_eval :
    program.runBlock (dialect code) ⟨.l11c230, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c23c_eval :
    program.runBlock (dialect code) ⟨.l11c23c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c248_eval :
    program.runBlock (dialect code) ⟨.l11c248, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c254_eval :
    program.runBlock (dialect code) ⟨.l11c254, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c25c_eval :
    program.runBlock (dialect code) ⟨.l11c25c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c260_eval :
    program.runBlock (dialect code) ⟨.l11c260, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c26f_eval :
    program.runBlock (dialect code) ⟨.l11c26f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c27e_eval :
    program.runBlock (dialect code) ⟨.l11c27e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c289_eval :
    program.runBlock (dialect code) ⟨.l11c289, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c28e_eval :
    program.runBlock (dialect code) ⟨.l11c28e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c294_eval :
    program.runBlock (dialect code) ⟨.l11c294, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c2bc_eval :
    program.runBlock (dialect code) ⟨.l11c2bc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c2c5_eval :
    program.runBlock (dialect code) ⟨.l11c2c5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c2d9_eval :
    program.runBlock (dialect code) ⟨.l11c2d9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c2f3_eval :
    program.runBlock (dialect code) ⟨.l11c2f3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c2fa_eval :
    program.runBlock (dialect code) ⟨.l11c2fa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c310_eval :
    program.runBlock (dialect code) ⟨.l11c310, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c320_eval :
    program.runBlock (dialect code) ⟨.l11c320, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c328_eval :
    program.runBlock (dialect code) ⟨.l11c328, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c334_eval :
    program.runBlock (dialect code) ⟨.l11c334, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c340_eval :
    program.runBlock (dialect code) ⟨.l11c340, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c34c_eval :
    program.runBlock (dialect code) ⟨.l11c34c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c350_eval :
    program.runBlock (dialect code) ⟨.l11c350, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c35f_eval :
    program.runBlock (dialect code) ⟨.l11c35f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c36e_eval :
    program.runBlock (dialect code) ⟨.l11c36e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c37d_eval :
    program.runBlock (dialect code) ⟨.l11c37d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c382_eval :
    program.runBlock (dialect code) ⟨.l11c382, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c387_eval :
    program.runBlock (dialect code) ⟨.l11c387, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c3a0_eval :
    program.runBlock (dialect code) ⟨.l11c3a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11c3ba_eval :
    program.runBlock (dialect code) ⟨.l11c3ba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
