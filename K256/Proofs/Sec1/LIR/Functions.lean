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

theorem rest_l100a20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a20 bytes_l100a20) (entryMap (live .l100a20))
      1 0x100a20 bytes_l100a20 b_l100a20 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x100a20 0xfe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100a20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a20 :=
  Rest.liftedBlock (rest_l100a20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a20 x hx)

theorem rest_l101dd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101dd0 bytes_l101dd0) (entryMap (live .l101dd0))
      6 0x101dd0 bytes_l101dd0 b_l101dd0 := by
  have f0 : InstrSpec 0x101dd0 [0x41, 0x56] (PushPre 0x101dd0 2) (pushR64Effect 0x101dd0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101dd0 2 14).toInstrSpec (push_r64_rex_effect_step 0x101dd0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x101dd2 [0x53] (PushPre 0x101dd2 1) (pushR64Effect 0x101dd2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x101dd2 1 3).toInstrSpec (push_r64_effect_step 0x101dd2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x101dd3 [0x48, 0x81, 0xEC, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101dd3) (subR64Imm32Effect 0x101dd3 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x101dd3 4 0xe8).toInstrSpec (sub_r64_imm32_effect_step 0x101dd3 0x48 0xec 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101dda [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x101dda) (movR64R64Effect 0x101dda 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x101dda 14 7).toInstrSpec (mov_r64_r64_effect_step 0x101dda 0x49 0xfe (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101ddd [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101ddd) (leaR64Effect 0x101ddd 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101ddd 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x101ddd 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101de5 [0xE8, 0xA6, 0x45, 0x00, 0x00] (PushPre 0x101de5 5) (callEffect (fun _ => 0x106390) 0x101dea)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101de5 0x106390 0x101dea).toInstrSpec (call_rel32_effect_step 0x101de5 0x45a6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dd3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101dda) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101ddd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101de5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106390) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l101dd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101dd0 :=
  Rest.liftedBlock (rest_l101dd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101dd0 x hx)

theorem rest_l101dea [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101dea bytes_l101dea) (entryMap (live .l101dea))
      3 0x101dea bytes_l101dea b_l101dea := by
  have f0 : InstrSpec 0x101dea [0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x101dea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101dea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101dea 3 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x101dea 3 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x101dea 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101df2 [0x48, 0x83, 0xFB, 0x01] (fun s => s.RIP = 0x101df2) (cmpR64Imm8Effect 0x101df2 3 0x1)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101df2 3 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x101df2 0x48 0xfb 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101df6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x101df6 4 0x6a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101dea [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101dea :=
  Rest.liftedBlock (rest_l101dea code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101dea x hx)

theorem rest_l101df8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101df8 bytes_l101df8) (entryMap (live .l101df8))
      4 0x101df8 bytes_l101df8 b_l101df8 := by
  have f0 : InstrSpec 0x101df8 [0x48, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101df8) (leaR64Effect 0x101df8 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101df8 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (lea_r64_effect_step 0x101df8 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101e00 [0x48, 0x8D, 0x7C, 0x24, 0x0F] (fun s => s.RIP = 0x101e00) (leaR64Effect 0x101e00 7 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x101e00 7 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x101e00 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e05 [0x31, 0xD2] (fun s => s.RIP = 0x101e05) (xorR32R32Effect 0x101e05 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101e05 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x101e05 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x101e07 [0xE8, 0xD4, 0xF7, 0x01, 0x00] (PushPre 0x101e07 5) (callEffect (fun _ => 0x1215e0) 0x101e0c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101e07 0x1215e0 0x101e0c).toInstrSpec (call_rel32_effect_step 0x101e07 0x1f7d4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e00) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e07) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1215e0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101df8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101df8 :=
  Rest.liftedBlock (rest_l101df8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101df8 x hx)

theorem rest_l101e0c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e0c bytes_l101e0c) (entryMap (live .l101e0c))
      7 0x101e0c bytes_l101e0c b_l101e0c := by
  have f0 : InstrSpec 0x101e0c [0x0F, 0xB6, 0x4C, 0x24, 0x0F] (LoadPre 0x101e0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101e0c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (movzx_r32_m8_effect_step 0x101e0c 1 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101e11 [0x48, 0x83, 0xF9, 0x06] (fun s => s.RIP = 0x101e11) (cmpR64Imm8Effect 0x101e11 1 0x6)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x101e11 1 0x6).toInstrSpec (cmp_r64_imm8_effect_step 0x101e11 0x48 0xf9 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e15 [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x101e15) (atFlags (condHolds 2) (setccR8Effect 0x101e15 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x101e15 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x101e15 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f3 : InstrSpec 0x101e18 [0xB2, 0x3D] (fun s => s.RIP = 0x101e18) (movR8Imm8Effect 0x101e18 2 2 0x3d)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR8Imm8Effect_footprint 0x101e18 2 2 0x3d).toInstrSpec (mov_r8_imm8_effect_step 0x101e18 0xb2 (by decide) 0x3d) pre_rip
  have f4 : InstrSpec 0x101e1a [0xD2, 0xEA] (fun s => s.RIP = 0x101e1a) (shrR8ClEffect 0x101e1a 2 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR8ClEffect_footprint 0x101e1a 2 2).toInstrSpec (shr_r8_cl_effect_step 0x101e1a 0xea (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101e1c [0x84, 0xD0] (fun s => s.RIP = 0x101e1c) (testR8R8Effect 0x101e1c 2 0 2)
      [.gpr 0, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x101e1c 2 0 2).toInstrSpec (test_r8_r8_effect_step 0x101e1c 0xd0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e11) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e15) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e18) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 53), (2, 59), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e1e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 65) (jcc_rel8_effect_step 0x101e1e 5 0x2c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101e0c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e0c :=
  Rest.liftedBlock (rest_l101e0c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e0c x hx)

theorem rest_l101e20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e20 bytes_l101e20) (entryMap (live .l101e20))
      7 0x101e20 bytes_l101e20 b_l101e20 := by
  have f0 : InstrSpec 0x101e20 [0xC7, 0x44, 0x24, 0x50, 0x03, 0x00, 0x00, 0x00] (StorePre 0x101e20 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101e20 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x101e20 8 (.sib 4 none 0 (.d8 0x50)) 0x3)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x101e20 8 (.sib 4 none 0 (.d8 0x50)) 0x3).toInstrSpec (mov_m32_imm32_effect_step 0x101e20 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101e28 [0x48, 0x8D, 0x54, 0x24, 0x50] (fun s => s.RIP = 0x101e28) (leaR64Effect 0x101e28 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x101e28 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (lea_r64_effect_step 0x101e28 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e2d [0xBE, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101e2d) (movR32Imm32Effect 0x101e2d 5 6 0xb)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x101e2d 5 6 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x101e2d 0xbe (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x101e32 [0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x101e32) (movR64Imm32Effect 0x101e32 7 0x202800)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x101e32 7 0x202800).toInstrSpec (mov_r64_imm32_effect_step 0x101e32 0x48 0xc7 (by decide) (by decide) (by decide) 0x202800) pre_rip
  have f4 : InstrSpec 0x101e39 [0x48, 0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00] (fun s => s.RIP = 0x101e39) (movR64Imm32Effect 0x101e39 1 0x2027e0)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x101e39 1 0x2027e0).toInstrSpec (mov_r64_imm32_effect_step 0x101e39 0x48 0xc1 (by decide) (by decide) (by decide) 0x2027e0) pre_rip
  have f5 : InstrSpec 0x101e40 [0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00] (fun s => s.RIP = 0x101e40) (movR64Imm32Effect 0x101e40 8 0x202810)
      [] [] [.reg 8, .rip] :=
    (movR64Imm32Effect_footprint 0x101e40 8 0x202810).toInstrSpec (mov_r64_imm32_effect_step 0x101e40 0x49 0xc0 (by decide) (by decide) (by decide) 0x202810) pre_rip
  have f6 : InstrSpec 0x101e47 [0xE8, 0x54, 0x77, 0x02, 0x00] (PushPre 0x101e47 5) (callEffect (fun _ => 0x1295a0) 0x101e4c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x101e47 0x1295a0 0x101e4c).toInstrSpec (call_rel32_effect_step 0x101e47 0x27754 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5)]) (p' := 0x101e28) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 54), (4, 4), (5, 5)]) (p' := 0x101e2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56)]) (p' := 0x101e32) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x101e39) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58)]) (p' := 0x101e40) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 60), (2, 54), (4, 4), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x101e47) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)]) (p' := 0x1295a0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l101e20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e20 :=
  Rest.liftedBlock (rest_l101e20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e20 x hx)

theorem rest_l101e4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e4c bytes_l101e4c) (entryMap (live .l101e4c))
      4 0x101e4c bytes_l101e4c b_l101e4c := by
  have f0 : InstrSpec 0x101e4c [0x48, 0x8B, 0x14, 0xCD, 0xB8, 0x22, 0x20, 0x00] (LoadPre 0x101e4c (fun s => AddrMode.addr (.abs (some 1) 3 0x2022b8) s (0x101e4c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101e4c 2 (.abs (some 1) 3 0x2022b8))
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101e4c 2 (.abs (some 1) 3 0x2022b8)).toInstrSpec (mov_r64_m64_effect_step 0x101e4c 0x48 (by decide) 2 (.abs (some 1) 3 0x2022b8) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101e54 [0x48, 0x8D, 0x74, 0x24, 0x0F] (fun s => s.RIP = 0x101e54) (leaR64Effect 0x101e54 6 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x101e54 6 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x101e54 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e59 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x101e59) (movR64R64Effect 0x101e59 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x101e59 7 14).toInstrSpec (mov_r64_r64_effect_step 0x101e59 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101e5c [0xFF, 0x15, 0x6E, 0x1F, 0x10, 0x00] (GoesTo (CallMemPre 0x101e5c (.rip 0x101f6e)) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e)))) 0x12a820) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x101e5c (.rip 0x101f6e)).toInstrSpec (call_m64_effect_step 0x101e5c (.rip 0x101f6e) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e54) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e59) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l101e4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e4c :=
  Rest.liftedBlock (rest_l101e4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e4c x hx)

theorem rest_l101e62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101e62 bytes_l101e62) (entryMap (live .l101e62))
      5 0x101e62 bytes_l101e62 b_l101e62 := by
  have f0 : InstrSpec 0x101e62 [0x89, 0xD8] (fun s => s.RIP = 0x101e62) (movR32R32Effect 0x101e62 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x101e62 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x101e62 0xd8 (by decide)) pre_rip
  have f1 : InstrSpec 0x101e64 [0x48, 0x81, 0xC4, 0xE8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101e64) (addR64Imm32Effect 0x101e64 4 0xe8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x101e64 4 0xe8).toInstrSpec (add_r64_imm32_effect_step 0x101e64 0x48 0xc4 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101e6b [0x5B] (PopPre 0x101e6b) (popR64Effect 0x101e6b 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e6b 1 3).toInstrSpec (pop_r64_effect_step 0x101e6b 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x101e6c [0x41, 0x5E] (PopPre 0x101e6c) (popR64Effect 0x101e6c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x101e6c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x101e6c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x101e6e [0xC3] (RetPre 0x101e6e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x101e6e).toInstrSpec (ret_effect_step 0x101e6e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e64) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101e6e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l101e62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101e62 :=
  Rest.liftedBlock (rest_l101e62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101e62 x hx)

theorem rest_l1148d0_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x1148d0 bytes_l1148d0) [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x114917 bytes_l1148d0_1 b_l1148d0_1 := by
  have f20 : InstrSpec 0x114917 [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x114917) (bswapR64Effect 0x114917 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x114917 3 6).toInstrSpec (bswap_r64_effect_step 0x114917 0x48 (by decide) 0xce (by decide)) pre_rip
  have f21 : InstrSpec 0x11491a [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x11491a) (movR64R64Effect 0x11491a 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11491a 0 7).toInstrSpec (mov_r64_r64_effect_step 0x11491a 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11491d [0x48, 0x0F, 0xC9] (fun s => s.RIP = 0x11491d) (bswapR64Effect 0x11491d 3 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR64Effect_footprint 0x11491d 3 1).toInstrSpec (bswap_r64_effect_step 0x11491d 0x48 (by decide) 0xc9 (by decide)) pre_rip
  have f23 : InstrSpec 0x114920 [0x48, 0x89, 0x17] (StorePre 0x114920 3 (fun s => AddrMode.addr (.base 7 .none) s (0x114920 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x114920 2 (.base 7 .none))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x114920 2 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x114920 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x114923 [0x4C, 0x89, 0x57, 0x08] (StorePre 0x114923 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x114923 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114923 10 (.base 7 (.d8 0x8)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x114923 10 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x114923 0x4c (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x114927 [0x48, 0x89, 0x77, 0x10] (StorePre 0x114927 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x114927 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114927 6 (.base 7 (.d8 0x10)))
      [.gpr 6, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x114927 6 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x114927 0x48 (by decide) 6 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x11492b [0x48, 0x89, 0x4F, 0x18] (StorePre 0x11492b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x11492b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11492b 1 (.base 7 (.d8 0x18)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x11492b 1 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11492b 0x48 (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x11492f [0xC3] (RetPre 0x11492f) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11492f).toInstrSpec (ret_effect_step 0x11492f) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11491a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11491d) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114920) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114923) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114927) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11492b) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 4), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11492f) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f27 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 104) f27 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 105) (ρ' := [(0, 95), (1, 97), (2, 89), (3, 3), (4, 104), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f27 (by decide) rfl rfl rfl (by decide)

theorem rest_l1148d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1148d0 bytes_l1148d0) (entryMap (live .l1148d0))
      28 0x1148d0 bytes_l1148d0 b_l1148d0 := by
  have f0 : InstrSpec 0x1148d0 [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x1148d0 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1148d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d0 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1148d0 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1148d0 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1148d4 [0x4C, 0x8B, 0x46, 0x10] (LoadPre 0x1148d4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1148d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d4 8 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1148d4 8 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1148d4 0x4c (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1148d8 [0x4C, 0x8B, 0x4E, 0x18] (LoadPre 0x1148d8 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1148d8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d8 9 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1148d8 9 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1148d8 0x4c (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1148dc [0x48, 0x8B, 0x56, 0x20] (LoadPre 0x1148dc (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1148dc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148dc 2 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1148dc 2 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1148dc 0x48 (by decide) 2 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1148e0 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x1148e0) (movR64R64Effect 0x1148e0 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1148e0 1 0).toInstrSpec (mov_r64_r64_effect_step 0x1148e0 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1148e3 [0x48, 0xC1, 0xE1, 0x34] (fun s => s.RIP = 0x1148e3) (shlR64Effect 0x1148e3 4 1 52)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x1148e3 4 1 52).toInstrSpec (shl_r64_imm8_effect_step 0x1148e3 0x48 0xe1 0x34 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1148e7 [0x48, 0x0B, 0x0E] (LoadPre 0x1148e7 (fun s => AddrMode.addr (.base 6 .none) s (0x1148e7 + BitVec.ofNat 64 3)) 8) (orR64M64Effect 0x1148e7 1 (.base 6 .none))
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR64M64Effect_footprint 0x1148e7 1 (.base 6 .none)).toInstrSpec (or_r64_m64_effect_step 0x1148e7 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1148ea [0x48, 0xC1, 0xE8, 0x0C] (fun s => s.RIP = 0x1148ea) (shrR64Effect 0x1148ea 4 0 12)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x1148ea 4 0 12).toInstrSpec (shr_r64_imm8_effect_step 0x1148ea 0x48 0xe8 0xc (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1148ee [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x1148ee) (movR64R64Effect 0x1148ee 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1148ee 6 8).toInstrSpec (mov_r64_r64_effect_step 0x1148ee 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1148f1 [0x48, 0xC1, 0xE6, 0x28] (fun s => s.RIP = 0x1148f1) (shlR64Effect 0x1148f1 4 6 40)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64Effect_footprint 0x1148f1 4 6 40).toInstrSpec (shl_r64_imm8_effect_step 0x1148f1 0x48 0xe6 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1148f5 [0x48, 0x09, 0xC6] (fun s => s.RIP = 0x1148f5) (orR64R64Effect 0x1148f5 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1148f5 6 0).toInstrSpec (or_r64_r64_effect_step 0x1148f5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1148f8 [0x49, 0xC1, 0xE8, 0x18] (fun s => s.RIP = 0x1148f8) (shrR64Effect 0x1148f8 4 8 24)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x1148f8 4 8 24).toInstrSpec (shr_r64_imm8_effect_step 0x1148f8 0x49 0xe8 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1148fc [0x4D, 0x89, 0xCA] (fun s => s.RIP = 0x1148fc) (movR64R64Effect 0x1148fc 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x1148fc 10 9).toInstrSpec (mov_r64_r64_effect_step 0x1148fc 0x4d 0xca (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1148ff [0x49, 0xC1, 0xE2, 0x1C] (fun s => s.RIP = 0x1148ff) (shlR64Effect 0x1148ff 4 10 28)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR64Effect_footprint 0x1148ff 4 10 28).toInstrSpec (shl_r64_imm8_effect_step 0x1148ff 0x49 0xe2 0x1c (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x114903 [0x4D, 0x09, 0xC2] (fun s => s.RIP = 0x114903) (orR64R64Effect 0x114903 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (orR64R64Effect_footprint 0x114903 10 8).toInstrSpec (or_r64_r64_effect_step 0x114903 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x114906 [0x49, 0xC1, 0xE9, 0x24] (fun s => s.RIP = 0x114906) (shrR64Effect 0x114906 4 9 36)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64Effect_footprint 0x114906 4 9 36).toInstrSpec (shr_r64_imm8_effect_step 0x114906 0x49 0xe9 0x24 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11490a [0x48, 0xC1, 0xE2, 0x10] (fun s => s.RIP = 0x11490a) (shlR64Effect 0x11490a 4 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR64Effect_footprint 0x11490a 4 2 16).toInstrSpec (shl_r64_imm8_effect_step 0x11490a 0x48 0xe2 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11490e [0x4C, 0x09, 0xCA] (fun s => s.RIP = 0x11490e) (orR64R64Effect 0x11490e 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11490e 2 9).toInstrSpec (or_r64_r64_effect_step 0x11490e 0x4c 0xca (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x114911 [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x114911) (bswapR64Effect 0x114911 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x114911 3 2).toInstrSpec (bswap_r64_effect_step 0x114911 0x48 (by decide) 0xca (by decide)) pre_rip
  have f19 : InstrSpec 0x114914 [0x49, 0x0F, 0xCA] (fun s => s.RIP = 0x114914) (bswapR64Effect 0x114914 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR64Effect_footprint 0x114914 3 10).toInstrSpec (bswap_r64_effect_step 0x114914 0x49 (by decide) 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148dc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148e0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148e3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 63), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148e7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ea) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ee) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148f1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148f5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 55), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148f8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148fc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (10, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148ff) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (10, 79), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114903) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 57), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114906) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 67), (1, 65), (2, 59), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11490a) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 67), (1, 65), (2, 85), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11490e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 67), (1, 65), (2, 87), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114911) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114914) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 67), (1, 65), (2, 89), (3, 3), (4, 4), (5, 5), (6, 73), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114917) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1148d0_1 code

theorem block_l1148d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1148d0 :=
  Rest.liftedBlock (rest_l1148d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1148d0 x hx)

theorem rest_l124290 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124290 bytes_l124290) (entryMap (live .l124290))
      8 0x124290 bytes_l124290 b_l124290 := by
  have f0 : InstrSpec 0x124290 [0x55] (PushPre 0x124290 1) (pushR64Effect 0x124290 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124290 1 5).toInstrSpec (push_r64_effect_step 0x124290 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x124291 [0x41, 0x56] (PushPre 0x124291 2) (pushR64Effect 0x124291 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124291 2 14).toInstrSpec (push_r64_rex_effect_step 0x124291 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124293 [0x53] (PushPre 0x124293 1) (pushR64Effect 0x124293 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124293 1 3).toInstrSpec (push_r64_effect_step 0x124293 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124294 [0x48, 0x83, 0xEC, 0x60] (fun s => s.RIP = 0x124294) (subR64Imm8Effect 0x124294 4 0x60)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x124294 4 0x60).toInstrSpec (sub_r64_imm8_effect_step 0x124294 0x48 0xec 0x60 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x124298 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x124298) (movR64R64Effect 0x124298 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x124298 3 7).toInstrSpec (mov_r64_r64_effect_step 0x124298 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12429b [0x8B, 0x46, 0x18] (LoadPre 0x12429b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12429b + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x12429b 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x12429b 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x12429b 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12429e [0x3B, 0x46, 0x1C] (LoadPre 0x12429e (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x12429e + BitVec.ofNat 64 3)) 4) (cmpR32M32Effect 0x12429e 3 0 (.base 6 (.d8 0x1c)))
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR32M32Effect_footprint 0x12429e 3 0 (.base 6 (.d8 0x1c))).toInstrSpec (cmp_r32_m32_effect_step 0x12429e 0 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124291) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124293) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124294) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124298) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12429b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12429e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242a1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x1242a1 6 0x7f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124290 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124290 :=
  Rest.liftedBlock (rest_l124290 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124290 x hx)

theorem rest_l1242a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1242a3 bytes_l1242a3) (entryMap (live .l1242a3))
      15 0x1242a3 bytes_l1242a3 b_l1242a3 := by
  have f0 : InstrSpec 0x1242a3 [0x89, 0xD5] (fun s => s.RIP = 0x1242a3) (movR32R32Effect 0x1242a3 2 5 2)
      [.gpr 2] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x1242a3 2 5 2).toInstrSpec (mov_r32_r32_effect_step 0x1242a3 0xd5 (by decide)) pre_rip
  have f1 : InstrSpec 0x1242a5 [0x41, 0x89, 0xCE] (fun s => s.RIP = 0x1242a5) (movR32R32Effect 0x1242a5 3 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x1242a5 3 14 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x1242a5 0x41 0xce (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1242a8 [0x48, 0x8B, 0x06] (LoadPre 0x1242a8 (fun s => AddrMode.addr (.base 6 .none) s (0x1242a8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1242a8 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1242a8 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1242a8 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1242ab [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x1242ab (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1242ab + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242ab 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1242ab 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1242ab 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1242af [0x0F, 0xB6, 0x56, 0x20] (LoadPre 0x1242af (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1242af + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1242af 4 2 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1242af 4 2 (.base 6 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x1242af 2 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1242b3 [0x48, 0x8B, 0x7E, 0x18] (LoadPre 0x1242b3 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1242b3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242b3 7 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1242b3 7 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1242b3 0x48 (by decide) 7 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1242b7 [0x48, 0x89, 0x7C, 0x24, 0x50] (StorePre 0x1242b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1242b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242b7 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1242b7 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x1242b7 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1242bc [0x48, 0x8B, 0x76, 0x10] (LoadPre 0x1242bc (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1242bc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1242bc 6 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1242bc 6 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1242bc 0x48 (by decide) 6 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1242c0 [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x1242c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1242c0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242c0 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1242c0 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x1242c0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1242c5 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x1242c5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1242c5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242c5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1242c5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x1242c5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1242ca [0x48, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x1242ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1242ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1242ca 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1242ca 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1242ca 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1242cf [0x88, 0x54, 0x24, 0x58] (StorePre 0x1242cf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1242cf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1242cf 4 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1242cf 4 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m8_r8_effect_step 0x1242cf 2 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1242d3 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x1242d3) (movR64R64Effect 0x1242d3 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1242d3 7 4).toInstrSpec (mov_r64_r64_effect_step 0x1242d3 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1242d6 [0x48, 0x8D, 0x74, 0x24, 0x38] (fun s => s.RIP = 0x1242d6) (leaR64Effect 0x1242d6 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1242d6 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x1242d6 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1242db [0xE8, 0x50, 0x01, 0x00, 0x00] (PushPre 0x1242db 5) (callEffect (fun _ => 0x124430) 0x1242e0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1242db 0x124430 0x1242e0).toInstrSpec (call_rel32_effect_step 0x1242db 0x150 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242a8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 2), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242af) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242b3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242b7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242bc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242c0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242c5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242ca) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242cf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242d3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 66), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242d6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 4), (5, 53), (6, 74), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242db) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 57), (1, 59), (2, 61), (3, 3), (4, 76), (5, 53), (6, 74), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124430) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 78) (by decide) (by decide) rfl rfl

theorem block_l1242a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1242a3 :=
  Rest.liftedBlock (rest_l1242a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1242a3 x hx)

theorem rest_l1242e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1242e0 bytes_l1242e0) (entryMap (live .l1242e0))
      4 0x1242e0 bytes_l1242e0 b_l1242e0 := by
  have f0 : InstrSpec 0x1242e0 [0x8B, 0x0C, 0x24] (LoadPre 0x1242e0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1242e0 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1242e0 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1242e0 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x1242e0 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1242e3 [0x48, 0x8B, 0x44, 0x24, 0x04] (LoadPre 0x1242e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1242e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1242e3 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1242e3 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r64_m64_effect_step 0x1242e3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1242e8 [0x83, 0xF9, 0x02] (fun s => s.RIP = 0x1242e8) (cmpR32Imm8Effect 0x1242e8 3 1 0x2)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1242e8 3 1 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1242e8 0xf9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242e3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242e8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242eb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1242eb 5 0x3e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1242e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1242e0 :=
  Rest.liftedBlock (rest_l1242e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1242e0 x hx)

theorem rest_l1242ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1242ed bytes_l1242ed) (entryMap (live .l1242ed))
      10 0x1242ed bytes_l1242ed b_l1242ed := by
  have f0 : InstrSpec 0x1242ed [0x8D, 0x50, 0xEA] (fun s => s.RIP = 0x1242ed) (leaR32Effect 0x1242ed 3 2 (.base 0 (.d8 0xea)))
      [.gpr 0] [] [.reg 2, .rip] :=
    (leaR32Effect_footprint 0x1242ed 3 2 (.base 0 (.d8 0xea))).toInstrSpec (lea_r32_effect_step 0x1242ed 2 (.base 0 (.d8 0xea)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1242f0 [0x89, 0xD6] (fun s => s.RIP = 0x1242f0) (movR32R32Effect 0x1242f0 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x1242f0 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x1242f0 0xd6 (by decide)) pre_rip
  have f2 : InstrSpec 0x1242f2 [0x40, 0xC0, 0xE6, 0x06] (fun s => s.RIP = 0x1242f2) (shlR8Effect 0x1242f2 4 6 6)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR8Effect_footprint 0x1242f2 4 6 6).toInstrSpec (shl_r8_imm8_rex_effect_step 0x1242f2 0x40 0xe6 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1242f6 [0x40, 0x80, 0xC6, 0x40] (fun s => s.RIP = 0x1242f6) (addR8Imm8Effect 0x1242f6 4 6 0x40)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR8Imm8Effect_footprint 0x1242f6 4 6 0x40).toInstrSpec (add_r8_imm8_rex_effect_step 0x1242f6 0x40 0xc6 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1242fa [0x31, 0xC9] (fun s => s.RIP = 0x1242fa) (xorR32R32Effect 0x1242fa 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1242fa 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1242fa 0xc9 (by decide)) pre_rip
  have f5 : InstrSpec 0x1242fc [0x80, 0xFA, 0x03] (fun s => s.RIP = 0x1242fc) (cmpR8Imm8Effect 0x1242fc 3 2 0x3)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1242fc 3 2 0x3).toInstrSpec (cmp_r8_imm8_effect_step 0x1242fc 0xfa 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1242ff [0x40, 0x0F, 0xB6, 0xD6] (fun s => s.RIP = 0x1242ff) (movzxR32R8Effect 0x1242ff 4 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1242ff 4 2 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1242ff 0x40 (by decide) 0xd6 (by decide)) pre_rip
  have f7 : InstrSpec 0x124303 [0x0F, 0x43, 0xD1] (fun s => s.RIP = 0x124303) (atFlags (condHolds 3) (cmovR32R32Effect 0x124303 3 2 1))
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (cmovR32R32Effect_footprint 0x124303 3 2 1 3).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x124303 3 0xd1 (by decide) c)) pre_rip
  have f8 : InstrSpec 0x124306 [0x40, 0x38, 0xEA] (fun s => s.RIP = 0x124306) (cmpR8R8Effect 0x124306 3 2 5)
      [.gpr 2, .gpr 5] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x124306 3 2 5).toInstrSpec (cmp_r8_r8_rex_effect_step 0x124306 0x40 0xea (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242f0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242f2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242f6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242fa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242fc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 53), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1242ff) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124303) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124306) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124309) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel32_effect_step 0x124309 5 0x102) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1242ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1242ed :=
  Rest.liftedBlock (rest_l1242ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1242ed x hx)

theorem rest_l12430f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12430f bytes_l12430f) (entryMap (live .l12430f))
      1 0x12430f bytes_l12430f b_l12430f := by
  have f0 : InstrSpec 0x12430f [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x12430f) (movzxR32R8Effect 0x12430f 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x12430f 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x12430f 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0)]) (p' := 0x124312) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12430f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12430f :=
  Rest.liftedBlock (rest_l12430f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12430f x hx)

theorem rest_l124322 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124322 bytes_l124322) (entryMap (live .l124322))
      2 0x124322 bytes_l124322 b_l124322 := by
  have f0 : InstrSpec 0x124322 [0xC6, 0x43, 0x04, 0x00] (StorePre 0x124322 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124322 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x124322 (.base 3 (.d8 0x4)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x124322 (.base 3 (.d8 0x4)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x124322 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124326) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel32_effect_step 0x124326 0xe9 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124322 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124322 :=
  Rest.liftedBlock (rest_l124322 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124322 x hx)

theorem rest_l12432b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12432b bytes_l12432b) (entryMap (live .l12432b))
      15 0x12432b bytes_l12432b b_l12432b := by
  have f0 : InstrSpec 0x12432b [0x8B, 0x54, 0x24, 0x34] (LoadPre 0x12432b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12432b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12432b 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x12432b 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x12432b 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12432f [0x89, 0x53, 0x34] (StorePre 0x12432f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x12432f + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12432f 2 (.base 3 (.d8 0x34)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12432f 2 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x12432f 2 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x124332 [0x48, 0x8B, 0x54, 0x24, 0x2C] (LoadPre 0x124332 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124332 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124332 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124332 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x124332 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124337 [0x48, 0x89, 0x53, 0x2C] (StorePre 0x124337 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124337 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124337 2 (.base 3 (.d8 0x2c)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124337 2 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x124337 0x48 (by decide) 2 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12433b [0x48, 0x8B, 0x54, 0x24, 0x24] (LoadPre 0x12433b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12433b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12433b 2 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12433b 2 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x12433b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x124340 [0x48, 0x89, 0x53, 0x24] (StorePre 0x124340 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124340 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124340 2 (.base 3 (.d8 0x24)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124340 2 (.base 3 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x124340 0x48 (by decide) 2 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124344 [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x124344 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124344 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124344 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124344 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x124344 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124349 [0x48, 0x89, 0x53, 0x1C] (StorePre 0x124349 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124349 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124349 2 (.base 3 (.d8 0x1c)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124349 2 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x124349 0x48 (by decide) 2 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12434d [0x48, 0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x12434d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x12434d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12434d 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12434d 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r64_m64_effect_step 0x12434d 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x124352 [0x48, 0x8B, 0x74, 0x24, 0x14] (LoadPre 0x124352 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124352 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124352 6 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124352 6 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x124352 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x124357 [0x48, 0x89, 0x73, 0x14] (StorePre 0x124357 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124357 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124357 6 (.base 3 (.d8 0x14)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124357 6 (.base 3 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x124357 0x48 (by decide) 6 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x12435b [0x48, 0x89, 0x53, 0x0C] (StorePre 0x12435b 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x12435b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12435b 2 (.base 3 (.d8 0xc)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x12435b 2 (.base 3 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x12435b 0x48 (by decide) 2 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12435f [0x89, 0x0B] (StorePre 0x12435f 2 (fun s => AddrMode.addr (.base 3 .none) s (0x12435f + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x12435f 1 (.base 3 .none))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12435f 1 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x12435f 1 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124361 [0x48, 0x89, 0x43, 0x04] (StorePre 0x124361 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124361 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124361 0 (.base 3 (.d8 0x4)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124361 0 (.base 3 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x124361 0x48 (by decide) 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12432f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124332) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124337) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 56), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12433b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124340) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124344) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124349) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 62), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12434d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124352) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124357) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12435b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12435f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124361) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124365) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 73) (jmp_rel32_effect_step 0x124365 0xb0 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12432b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12432b :=
  Rest.liftedBlock (rest_l12432b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12432b x hx)

theorem rest_l124411 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124411 bytes_l124411) (entryMap (live .l124411))
      1 0x124411 bytes_l124411 b_l124411 := by
  have f0 : InstrSpec 0x124411 [0x88, 0x4B, 0x04] (StorePre 0x124411 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124411 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x124411 3 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x124411 3 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m8_r8_effect_step 0x124411 1 (by decide) (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124414) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l124411 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124411 :=
  Rest.liftedBlock (rest_l124411 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124411 x hx)

theorem rest_l124414 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124414 bytes_l124414) (entryMap (live .l124414))
      1 0x124414 bytes_l124414 b_l124414 := by
  have f0 : InstrSpec 0x124414 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x124414 6 (fun s => AddrMode.addr (.base 3 .none) s (0x124414 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x124414 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x124414 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x124414 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12441a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l124414 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124414 :=
  Rest.liftedBlock (rest_l124414 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124414 x hx)

theorem rest_l12441a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12441a bytes_l12441a) (entryMap (live .l12441a))
      6 0x12441a bytes_l12441a b_l12441a := by
  have f0 : InstrSpec 0x12441a [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x12441a) (movR64R64Effect 0x12441a 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12441a 0 3).toInstrSpec (mov_r64_r64_effect_step 0x12441a 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12441d [0x48, 0x83, 0xC4, 0x60] (fun s => s.RIP = 0x12441d) (addR64Imm8Effect 0x12441d 4 0x60)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12441d 4 0x60).toInstrSpec (add_r64_imm8_effect_step 0x12441d 0x48 0xc4 0x60 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124421 [0x5B] (PopPre 0x124421) (popR64Effect 0x124421 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124421 1 3).toInstrSpec (pop_r64_effect_step 0x124421 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124422 [0x41, 0x5E] (PopPre 0x124422) (popR64Effect 0x124422 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124422 2 14).toInstrSpec (pop_r64_rex_effect_step 0x124422 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124424 [0x5D] (PopPre 0x124424) (popR64Effect 0x124424 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124424 1 5).toInstrSpec (pop_r64_effect_step 0x124424 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x124425 [0xC3] (RetPre 0x124425) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x124425).toInstrSpec (ret_effect_step 0x124425) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12441d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124421) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124422) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124424) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124425) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l12441a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12441a :=
  Rest.liftedBlock (rest_l12441a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12441a x hx)

theorem rest_l124ae0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124ae0 bytes_l124ae0) (entryMap (live .l124ae0))
      7 0x124ae0 bytes_l124ae0 b_l124ae0 := by
  have f0 : InstrSpec 0x124ae0 [0x41, 0x56] (PushPre 0x124ae0 2) (pushR64Effect 0x124ae0 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124ae0 2 14).toInstrSpec (push_r64_rex_effect_step 0x124ae0 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x124ae2 [0x53] (PushPre 0x124ae2 1) (pushR64Effect 0x124ae2 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x124ae2 1 3).toInstrSpec (push_r64_effect_step 0x124ae2 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x124ae3 [0x48, 0x83, 0xEC, 0x58] (fun s => s.RIP = 0x124ae3) (subR64Imm8Effect 0x124ae3 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x124ae3 4 0x58).toInstrSpec (sub_r64_imm8_effect_step 0x124ae3 0x48 0xec 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124ae7 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x124ae7) (movR64R64Effect 0x124ae7 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x124ae7 14 6).toInstrSpec (mov_r64_r64_effect_step 0x124ae7 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x124aea [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x124aea) (movR64R64Effect 0x124aea 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x124aea 3 7).toInstrSpec (mov_r64_r64_effect_step 0x124aea 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x124aed [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x124aed) (leaR64Effect 0x124aed 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124aed 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x124aed 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x124af2 [0xE8, 0x59, 0x09, 0x00, 0x00] (PushPre 0x124af2 5) (callEffect (fun _ => 0x125450) 0x124af7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124af2 0x125450 0x124af7).toInstrSpec (call_rel32_effect_step 0x124af2 0x959 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ae2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ae3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ae7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aea) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124aed) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 61), (4, 57), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124af2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 61), (4, 65), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125450) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l124ae0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124ae0 :=
  Rest.liftedBlock (rest_l124ae0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124ae0 x hx)

theorem rest_l124af7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124af7 bytes_l124af7) (entryMap (live .l124af7))
      7 0x124af7 bytes_l124af7 b_l124af7 := by
  have f0 : InstrSpec 0x124af7 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x124af7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124af7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124af7 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124af7 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x124af7 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124afb [0x48, 0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x124afb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124afb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124afb 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124afb 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x124afb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124b00 [0x48, 0x89, 0x0C, 0x24] (StorePre 0x124b00 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124b00 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b00 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b00 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x124b00 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124b04 [0x48, 0x8B, 0x4C, 0x24, 0x1C] (LoadPre 0x124b04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124b04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b04 1 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b04 1 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x124b04 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x124b09 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x124b09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124b09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124b09 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b09 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x124b09 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x124b0e [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124b0e) (cmpR32Imm8Effect 0x124b0e 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124b0e 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124b0e 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124afb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b00) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b04) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b09) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b0e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b11) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x124b11 5 0x3d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124af7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124af7 :=
  Rest.liftedBlock (rest_l124af7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124af7 x hx)

theorem rest_l124b13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b13 bytes_l124b13) (entryMap (live .l124b13))
      7 0x124b13 bytes_l124b13 b_l124b13 := by
  have f0 : InstrSpec 0x124b13 [0x48, 0x8B, 0x34, 0x24] (LoadPre 0x124b13 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124b13 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124b13 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124b13 6 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x124b13 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124b17 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x124b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124b17 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b17 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x124b17 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x124b17 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124b1c [0x48, 0x89, 0x74, 0x24, 0x48] (StorePre 0x124b1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x124b1c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124b1c 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b1c 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x124b1c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x124b21 [0x48, 0x89, 0x44, 0x24, 0x50] (StorePre 0x124b21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x124b21 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x124b21 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b21 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x124b21 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124b26 [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x124b26) (leaR64Effect 0x124b26 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x124b26 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x124b26 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x124b2b [0xBA, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x124b2b) (movR32Imm32Effect 0x124b2b 5 2 0x5)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x124b2b 5 2 0x5).toInstrSpec (mov_r32_imm32_effect_step 0x124b2b 0xba (by decide) 0x5) pre_rip
  have f6 : InstrSpec 0x124b30 [0xE8, 0x9B, 0x2B, 0x00, 0x00] (PushPre 0x124b30 5) (callEffect (fun _ => 0x1276d0) 0x124b35)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124b30 0x1276d0 0x124b35).toInstrSpec (call_rel32_effect_step 0x124b30 0x2b9b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b17) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b1c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b21) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b26) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b2b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b30) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l124b13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b13 :=
  Rest.liftedBlock (rest_l124b13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b13 x hx)

theorem rest_l124b35 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b35 bytes_l124b35) (entryMap (live .l124b35))
      3 0x124b35 bytes_l124b35 b_l124b35 := by
  have f0 : InstrSpec 0x124b35 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x124b35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x124b35 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124b35 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x124b35 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x124b35 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124b39 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x124b39) (cmpR32Imm8Effect 0x124b39 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x124b39 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x124b39 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b39) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b3c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x124b3c 5 0x52) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l124b35 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b35 :=
  Rest.liftedBlock (rest_l124b35 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b35 x hx)

theorem rest_l124b3e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b3e bytes_l124b3e) (entryMap (live .l124b3e))
      4 0x124b3e bytes_l124b3e b_l124b3e := by
  have f0 : InstrSpec 0x124b3e [0x48, 0x8D, 0x54, 0x24, 0x48] (fun s => s.RIP = 0x124b3e) (leaR64Effect 0x124b3e 2 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x124b3e 2 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x124b3e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124b43 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x124b43) (movR64R64Effect 0x124b43 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x124b43 7 3).toInstrSpec (mov_r64_r64_effect_step 0x124b43 0x48 0xdf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124b46 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x124b46) (movR64R64Effect 0x124b46 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x124b46 6 14).toInstrSpec (mov_r64_r64_effect_step 0x124b46 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x124b49 [0xE8, 0x72, 0x1C, 0x00, 0x00] (PushPre 0x124b49 5) (callEffect (fun _ => 0x1267c0) 0x124b4e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x124b49 0x1267c0 0x124b4e).toInstrSpec (call_rel32_effect_step 0x124b49 0x1c72 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b43) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b46) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b49) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1267c0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l124b3e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b3e :=
  Rest.liftedBlock (rest_l124b3e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b3e x hx)

theorem rest_l124b4e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b4e bytes_l124b4e) (entryMap (live .l124b4e))
      1 0x124b4e bytes_l124b4e b_l124b4e := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x124b4e 0x7f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124b4e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b4e :=
  Rest.liftedBlock (rest_l124b4e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b4e x hx)

theorem rest_l124b50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b50 bytes_l124b50) (entryMap (live .l124b50))
      16 0x124b50 bytes_l124b50 b_l124b50 := by
  have f0 : InstrSpec 0x124b50 [0x8B, 0x4C, 0x24, 0x44] (LoadPre 0x124b50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x124b50 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124b50 1 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x124b50 1 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x124b50 1 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124b54 [0x89, 0x4B, 0x34] (StorePre 0x124b54 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x124b54 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124b54 1 (.base 3 (.d8 0x34)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124b54 1 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x124b54 1 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x124b57 [0x48, 0x8B, 0x4C, 0x24, 0x3C] (LoadPre 0x124b57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x124b57 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b57 1 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b57 1 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r64_m64_effect_step 0x124b57 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124b5c [0x48, 0x89, 0x4B, 0x2C] (StorePre 0x124b5c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124b5c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b5c 1 (.base 3 (.d8 0x2c)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b5c 1 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x124b5c 0x48 (by decide) 1 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124b60 [0x48, 0x8B, 0x4C, 0x24, 0x34] (LoadPre 0x124b60 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124b60 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b60 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b60 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x124b60 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x124b65 [0x48, 0x89, 0x4B, 0x24] (StorePre 0x124b65 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124b65 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b65 1 (.base 3 (.d8 0x24)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b65 1 (.base 3 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x124b65 0x48 (by decide) 1 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124b69 [0x48, 0x8B, 0x4C, 0x24, 0x24] (LoadPre 0x124b69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124b69 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b69 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b69 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x124b69 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124b6e [0x48, 0x8B, 0x54, 0x24, 0x2C] (LoadPre 0x124b6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124b6e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b6e 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124b6e 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x124b6e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x124b73 [0x48, 0x89, 0x53, 0x1C] (StorePre 0x124b73 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124b73 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b73 2 (.base 3 (.d8 0x1c)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b73 2 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x124b73 0x48 (by decide) 2 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x124b77 [0x48, 0x89, 0x4B, 0x14] (StorePre 0x124b77 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124b77 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b77 1 (.base 3 (.d8 0x14)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b77 1 (.base 3 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x124b77 0x48 (by decide) 1 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x124b7b [0x48, 0x8B, 0x0C, 0x24] (LoadPre 0x124b7b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x124b7b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x124b7b 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b7b 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x124b7b 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x124b7f [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x124b7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x124b7f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b7f 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124b7f 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x124b7f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x124b84 [0x48, 0x89, 0x53, 0x0C] (StorePre 0x124b84 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x124b84 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b84 2 (.base 3 (.d8 0xc)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b84 2 (.base 3 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x124b84 0x48 (by decide) 2 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124b88 [0x48, 0x89, 0x4B, 0x04] (StorePre 0x124b88 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124b88 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124b88 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124b88 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x124b88 0x48 (by decide) 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x124b8c [0x89, 0x03] (StorePre 0x124b8c 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124b8c + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124b8c 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124b8c 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x124b8c 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b54) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b57) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b60) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b65) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b69) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b6e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b73) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b77) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b7b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b7f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b84) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b88) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b8c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b8e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 75) (jmp_rel8_effect_step 0x124b8e 0x3f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l124b50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b50 :=
  Rest.liftedBlock (rest_l124b50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b50 x hx)

theorem rest_l124b90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124b90 bytes_l124b90) (entryMap (live .l124b90))
      15 0x124b90 bytes_l124b90 b_l124b90 := by
  have f0 : InstrSpec 0x124b90 [0x48, 0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x124b90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x124b90 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b90 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x124b90 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x124b90 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x124b95 [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x124b95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x124b95 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124b95 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x124b95 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x124b95 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x124b9a [0x8B, 0x74, 0x24, 0x44] (LoadPre 0x124b9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x124b9a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x124b9a 6 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x124b9a 6 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x124b9a 6 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x124b9e [0x89, 0x73, 0x34] (StorePre 0x124b9e 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x124b9e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x124b9e 6 (.base 3 (.d8 0x34)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124b9e 6 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x124b9e 6 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x124ba1 [0x48, 0x8B, 0x74, 0x24, 0x3C] (LoadPre 0x124ba1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x124ba1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124ba1 6 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124ba1 6 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r64_m64_effect_step 0x124ba1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x124ba6 [0x48, 0x89, 0x73, 0x2C] (StorePre 0x124ba6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x124ba6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124ba6 6 (.base 3 (.d8 0x2c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124ba6 6 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x124ba6 0x48 (by decide) 6 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x124baa [0x48, 0x8B, 0x74, 0x24, 0x34] (LoadPre 0x124baa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x124baa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124baa 6 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124baa 6 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x124baa 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x124baf [0x48, 0x89, 0x73, 0x24] (StorePre 0x124baf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x124baf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124baf 6 (.base 3 (.d8 0x24)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124baf 6 (.base 3 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x124baf 0x48 (by decide) 6 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x124bb3 [0x48, 0x8B, 0x74, 0x24, 0x2C] (LoadPre 0x124bb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x124bb3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124bb3 6 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124bb3 6 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x124bb3 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x124bb8 [0x48, 0x89, 0x73, 0x1C] (StorePre 0x124bb8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x124bb8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bb8 6 (.base 3 (.d8 0x1c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124bb8 6 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x124bb8 0x48 (by decide) 6 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x124bbc [0x48, 0x8B, 0x74, 0x24, 0x24] (LoadPre 0x124bbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x124bbc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x124bbc 6 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x124bbc 6 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x124bbc 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x124bc1 [0x48, 0x89, 0x73, 0x14] (StorePre 0x124bc1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x124bc1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bc1 6 (.base 3 (.d8 0x14)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124bc1 6 (.base 3 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x124bc1 0x48 (by decide) 6 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x124bc5 [0x48, 0x89, 0x53, 0x0C] (StorePre 0x124bc5 4 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x124bc5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bc5 2 (.base 3 (.d8 0xc)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124bc5 2 (.base 3 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x124bc5 0x48 (by decide) 2 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x124bc9 [0x89, 0x03] (StorePre 0x124bc9 2 (fun s => AddrMode.addr (.base 3 .none) s (0x124bc9 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x124bc9 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x124bc9 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x124bc9 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x124bcb [0x48, 0x89, 0x4B, 0x04] (StorePre 0x124bcb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x124bcb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x124bcb 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x124bcb 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x124bcb 0x48 (by decide) 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b95) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b9a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124b9e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ba1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 60), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124ba6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 60), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124baa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124baf) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bb3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bb8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bbc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bc1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bc5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bc9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bcb) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bcf) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 75) (by decide) rfl

theorem block_l124b90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124b90 :=
  Rest.liftedBlock (rest_l124b90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124b90 x hx)

theorem rest_l124bcf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x124bcf bytes_l124bcf) (entryMap (live .l124bcf))
      5 0x124bcf bytes_l124bcf b_l124bcf := by
  have f0 : InstrSpec 0x124bcf [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x124bcf) (movR64R64Effect 0x124bcf 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x124bcf 0 3).toInstrSpec (mov_r64_r64_effect_step 0x124bcf 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x124bd2 [0x48, 0x83, 0xC4, 0x58] (fun s => s.RIP = 0x124bd2) (addR64Imm8Effect 0x124bd2 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x124bd2 4 0x58).toInstrSpec (add_r64_imm8_effect_step 0x124bd2 0x48 0xc4 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x124bd6 [0x5B] (PopPre 0x124bd6) (popR64Effect 0x124bd6 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124bd6 1 3).toInstrSpec (pop_r64_effect_step 0x124bd6 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x124bd7 [0x41, 0x5E] (PopPre 0x124bd7) (popR64Effect 0x124bd7 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x124bd7 2 14).toInstrSpec (pop_r64_rex_effect_step 0x124bd7 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x124bd9 [0xC3] (RetPre 0x124bd9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x124bd9).toInstrSpec (ret_effect_step 0x124bd9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bd2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bd6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bd7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x124bd9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l124bcf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l124bcf :=
  Rest.liftedBlock (rest_l124bcf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l124bcf x hx)

theorem rest_l127670 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127670 bytes_l127670) (entryMap (live .l127670))
      7 0x127670 bytes_l127670 b_l127670 := by
  have f0 : InstrSpec 0x127670 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x127670) (movR64R64Effect 0x127670 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127670 0 7).toInstrSpec (mov_r64_r64_effect_step 0x127670 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127673 [0x0F, 0xB6, 0x0E] (LoadPre 0x127673 (fun s => AddrMode.addr (.base 6 .none) s (0x127673 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x127673 3 1 (.base 6 .none))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x127673 3 1 (.base 6 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x127673 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127676 [0xC1, 0xE9, 0x07] (fun s => s.RIP = 0x127676) (shrR32Effect 0x127676 3 1 7)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x127676 3 1 7).toInstrSpec (shr_r32_imm8_effect_step 0x127676 0xe9 0x7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127679 [0xFF, 0xC1] (fun s => s.RIP = 0x127679) (incR32Effect 0x127679 2 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR32Effect_footprint 0x127679 2 1).toInstrSpec (inc_r32_effect_step 0x127679 0xc1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12767b [0x89, 0x4F, 0x04] (StorePre 0x12767b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x12767b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12767b 1 (.base 7 (.d8 0x4)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12767b 1 (.base 7 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x12767b 1 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12767e [0xC7, 0x07, 0x02, 0x00, 0x00, 0x00] (StorePre 0x12767e 6 (fun s => AddrMode.addr (.base 7 .none) s (0x12767e + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12767e 6 (.base 7 .none) 0x2)
      [.gpr 7] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x12767e 6 (.base 7 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x12767e (.base 7 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127684 [0xC3] (RetPre 0x127684) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127684).toInstrSpec (ret_effect_step 0x127684) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127673) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127676) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127679) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12767b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12767e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127684) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 59), (2, 2), (3, 3), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l127670 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127670 :=
  Rest.liftedBlock (rest_l127670 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127670 x hx)

theorem rest_l127690 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127690 bytes_l127690) (entryMap (live .l127690))
      4 0x127690 bytes_l127690 b_l127690 := by
  have f0 : InstrSpec 0x127690 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x127690) (movR64R64Effect 0x127690 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127690 0 7).toInstrSpec (mov_r64_r64_effect_step 0x127690 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127693 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x127693) (movR64R64Effect 0x127693 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x127693 1 2).toInstrSpec (mov_r64_r64_effect_step 0x127693 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127696 [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x127696) (shrR64Effect 0x127696 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x127696 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x127696 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127693) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127696) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 58) f2 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x127696 4 1 32 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12769a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x12769a 4 0xe) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127690 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127690 :=
  Rest.liftedBlock (rest_l127690 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127690 x hx)

theorem rest_l12769c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12769c bytes_l12769c) (entryMap (live .l12769c))
      5 0x12769c bytes_l12769c b_l12769c := by
  have f0 : InstrSpec 0x12769c [0xBE, 0x0C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12769c) (movR32Imm32Effect 0x12769c 5 6 0xc)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x12769c 5 6 0xc).toInstrSpec (mov_r32_imm32_effect_step 0x12769c 0xbe (by decide) 0xc) pre_rip
  have f1 : InstrSpec 0x1276a1 [0x31, 0xC9] (fun s => s.RIP = 0x1276a1) (xorR32R32Effect 0x1276a1 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1276a1 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x1276a1 0xc9 (by decide)) pre_rip
  have f2 : InstrSpec 0x1276a3 [0x89, 0x08] (StorePre 0x1276a3 2 (fun s => AddrMode.addr (.base 0 .none) s (0x1276a3 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1276a3 1 (.base 0 .none))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1276a3 1 (.base 0 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1276a3 1 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1276a5 [0x48, 0x89, 0x70, 0x08] (StorePre 0x1276a5 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1276a5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1276a5 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1276a5 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1276a5 0x48 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1276a9 [0xC3] (RetPre 0x1276a9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1276a9).toInstrSpec (ret_effect_step 0x1276a9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276a5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276a9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 60), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l12769c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12769c :=
  Rest.liftedBlock (rest_l12769c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12769c x hx)

theorem rest_l1276aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1276aa bytes_l1276aa) (entryMap (live .l1276aa))
      9 0x1276aa bytes_l1276aa b_l1276aa := by
  have f0 : InstrSpec 0x1276aa [0x48, 0x89, 0x50, 0x10] (StorePre 0x1276aa 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x1276aa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1276aa 2 (.base 0 (.d8 0x10)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1276aa 2 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x1276aa 0x48 (by decide) 2 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1276ae [0x48, 0xC7, 0x40, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1276ae 8 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x1276ae + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1276ae (.base 0 (.d8 0x18)) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1276ae (.base 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1276ae 0x48 (by decide) (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1276b6 [0x89, 0x50, 0x20] (StorePre 0x1276b6 3 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x1276b6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1276b6 2 (.base 0 (.d8 0x20)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1276b6 2 (.base 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_low_effect_step 0x1276b6 2 (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1276b9 [0xC7, 0x40, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1276b9 7 (fun s => AddrMode.addr (.base 0 (.d8 0x24)) s (0x1276b9 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1276b9 7 (.base 0 (.d8 0x24)) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1276b9 7 (.base 0 (.d8 0x24)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x1276b9 (.base 0 (.d8 0x24)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1276c0 [0xC6, 0x40, 0x28, 0x00] (StorePre 0x1276c0 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x1276c0 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1276c0 (.base 0 (.d8 0x28)) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1276c0 (.base 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1276c0 (.base 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1276c4 [0xB9, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1276c4) (movR32Imm32Effect 0x1276c4 5 1 0x2)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1276c4 5 1 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x1276c4 0xb9 (by decide) 0x2) pre_rip
  have f6 : InstrSpec 0x1276c9 [0x89, 0x08] (StorePre 0x1276c9 2 (fun s => AddrMode.addr (.base 0 .none) s (0x1276c9 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1276c9 1 (.base 0 .none))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1276c9 1 (.base 0 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1276c9 1 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1276cb [0x48, 0x89, 0x70, 0x08] (StorePre 0x1276cb 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1276cb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1276cb 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1276cb 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1276cb 0x48 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1276cf [0xC3] (RetPre 0x1276cf) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1276cf).toInstrSpec (ret_effect_step 0x1276cf) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276ae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276b6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276b9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276c0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276c4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276c9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276cb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276cf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 64) (ρ' := [(0, 0), (1, 58), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l1276aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1276aa :=
  Rest.liftedBlock (rest_l1276aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1276aa x hx)

theorem rest_l1276d0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1276d0 bytes_l1276d0) (entryMap (live .l1276d0))
      3 0x1276d0 bytes_l1276d0 b_l1276d0 := by
  have f0 : InstrSpec 0x1276d0 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x1276d0) (movR64R64Effect 0x1276d0 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1276d0 0 7).toInstrSpec (mov_r64_r64_effect_step 0x1276d0 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1276d3 [0x40, 0x38, 0xD6] (fun s => s.RIP = 0x1276d3) (cmpR8R8Effect 0x1276d3 3 6 2)
      [.gpr 6, .gpr 2] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x1276d3 3 6 2).toInstrSpec (cmp_r8_r8_rex_effect_step 0x1276d3 0x40 0xd6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1276d6 5 0x4e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1276d0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1276d0 :=
  Rest.liftedBlock (rest_l1276d0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1276d0 x hx)

theorem rest_l1276d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1276d8 bytes_l1276d8) (entryMap (live .l1276d8))
      10 0x1276d8 bytes_l1276d8 b_l1276d8 := by
  have f0 : InstrSpec 0x1276d8 [0x41, 0x89, 0xF0] (fun s => s.RIP = 0x1276d8) (movR32R32Effect 0x1276d8 3 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x1276d8 3 8 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x1276d8 0x41 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1276db [0x41, 0xC1, 0xE8, 0x08] (fun s => s.RIP = 0x1276db) (shrR32Effect 0x1276db 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x1276db 4 8 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1276db 0x41 0xe8 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1276df [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x1276df) (movR64R64Effect 0x1276df 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1276df 1 6).toInstrSpec (mov_r64_r64_effect_step 0x1276df 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1276e2 [0x48, 0xC1, 0xE9, 0x20] (fun s => s.RIP = 0x1276e2) (shrR64Effect 0x1276e2 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x1276e2 4 1 32).toInstrSpec (shr_r64_imm8_effect_step 0x1276e2 0x48 0xe9 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1276e6 [0x41, 0x89, 0xD1] (fun s => s.RIP = 0x1276e6) (movR32R32Effect 0x1276e6 3 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1276e6 3 9 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x1276e6 0x41 0xd1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1276e9 [0x41, 0xC1, 0xE9, 0x08] (fun s => s.RIP = 0x1276e9) (shrR32Effect 0x1276e9 4 9 8)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x1276e9 4 9 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1276e9 0x41 0xe9 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1276ed [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x1276ed) (movR64R64Effect 0x1276ed 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1276ed 7 2).toInstrSpec (mov_r64_r64_effect_step 0x1276ed 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1276f0 [0x48, 0xC1, 0xEF, 0x20] (fun s => s.RIP = 0x1276f0) (shrR64Effect 0x1276f0 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x1276f0 4 7 32).toInstrSpec (shr_r64_imm8_effect_step 0x1276f0 0x48 0xef 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1276f4 [0x40, 0x80, 0xFE, 0x18] (fun s => s.RIP = 0x1276f4) (cmpR8Imm8Effect 0x1276f4 4 6 0x18)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1276f4 4 6 0x18).toInstrSpec (cmp_r8_imm8_rex_effect_step 0x1276f4 0x40 0xfe 0x18 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276db) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276e2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276e6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276e9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276ed) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276f0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276f4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276f8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x1276f8 4 0x10) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1276d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1276d8 :=
  Rest.liftedBlock (rest_l1276d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1276d8 x hx)

theorem rest_l1276fa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1276fa bytes_l1276fa) (entryMap (live .l1276fa))
      3 0x1276fa bytes_l1276fa b_l1276fa := by
  have f0 : InstrSpec 0x1276fa [0x44, 0x0F, 0xB6, 0xD6] (fun s => s.RIP = 0x1276fa) (movzxR32R8Effect 0x1276fa 4 10 6)
      [.gpr 6] [] [.reg 10, .rip] :=
    (movzxR32R8Effect_footprint 0x1276fa 4 10 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x1276fa 0x44 (by decide) 0xd6 (by decide)) pre_rip
  have f1 : InstrSpec 0x1276fe [0x41, 0x83, 0xFA, 0x17] (fun s => s.RIP = 0x1276fe) (cmpR32Imm8Effect 0x1276fe 4 10 0x17)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1276fe 4 10 0x17).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x1276fe 0x41 0xfa 0x17 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276fe) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127702) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x127702 4 0x6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1276fa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1276fa :=
  Rest.liftedBlock (rest_l1276fa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1276fa x hx)

theorem rest_l127704 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127704 bytes_l127704) (entryMap (live .l127704))
      2 0x127704 bytes_l127704 b_l127704 := by
  have f0 : InstrSpec 0x127704 [0x41, 0x83, 0xFA, 0x16] (fun s => s.RIP = 0x127704) (cmpR32Imm8Effect 0x127704 4 10 0x16)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x127704 4 10 0x16).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x127704 0x41 0xfa 0x16 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127708) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127708 5 0x11) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127704 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127704 :=
  Rest.liftedBlock (rest_l127704 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127704 x hx)

theorem rest_l12770a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12770a bytes_l12770a) (entryMap (live .l12770a))
      6 0x12770a bytes_l12770a b_l12770a := by
  have f0 : InstrSpec 0x12770a [0x45, 0x38, 0xC8] (fun s => s.RIP = 0x12770a) (cmpR8R8Effect 0x12770a 3 8 9)
      [.gpr 8, .gpr 9] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x12770a 3 8 9).toInstrSpec (cmp_r8_r8_rex_effect_step 0x12770a 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12770d [0x41, 0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x12770d) (atFlags (condHolds 4) (setccR8Effect 0x12770d 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x12770d 4 8 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x12770d 4 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f2 : InstrSpec 0x127711 [0x39, 0xF9] (fun s => s.RIP = 0x127711) (cmpR32R32Effect 0x127711 2 1 7)
      [.gpr 1, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127711 2 1 7).toInstrSpec (cmp_r32_r32_effect_step 0x127711 0xf9 (by decide)) pre_rip
  have f3 : InstrSpec 0x127713 [0x0F, 0x94, 0xC1] (fun s => s.RIP = 0x127713) (atFlags (condHolds 4) (setccR8Effect 0x127713 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x127713 3 1 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x127713 4 0xc1 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x127716 [0x44, 0x84, 0xC1] (fun s => s.RIP = 0x127716) (testR8R8Effect 0x127716 3 1 8)
      [.gpr 1, .gpr 8] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x127716 3 1 8).toInstrSpec (test_r8_r8_rex_effect_step 0x127716 0x44 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12770d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127711) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127713) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127716) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127719) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x127719 4 0xb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12770a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12770a :=
  Rest.liftedBlock (rest_l12770a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12770a x hx)

theorem rest_l12771b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12771b bytes_l12771b) (entryMap (live .l12771b))
      3 0x12771b bytes_l12771b b_l12771b := by
  have f0 : InstrSpec 0x12771b [0x48, 0x89, 0x70, 0x04] (StorePre 0x12771b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x12771b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12771b 6 (.base 0 (.d8 0x4)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x12771b 6 (.base 0 (.d8 0x4))).toInstrSpec (mov_m64_r64_effect_step 0x12771b 0x48 (by decide) 6 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12771f [0xC7, 0x00, 0x02, 0x00, 0x00, 0x00] (StorePre 0x12771f 6 (fun s => AddrMode.addr (.base 0 .none) s (0x12771f + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12771f 6 (.base 0 .none) 0x2)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x12771f 6 (.base 0 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x12771f (.base 0 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127725 [0xC3] (RetPre 0x127725) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127725).toInstrSpec (ret_effect_step 0x127725) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12771f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127725) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l12771b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12771b :=
  Rest.liftedBlock (rest_l12771b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12771b x hx)

theorem rest_l127726 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127726 bytes_l127726) (entryMap (live .l127726))
      5 0x127726 bytes_l127726 b_l127726 := by
  have f0 : InstrSpec 0x127726 [0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x127726 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127726 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127726 6 (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127726 6 (.base 0 .none) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x127726 (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12772c [0xC6, 0x40, 0x08, 0x11] (StorePre 0x12772c 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x12772c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12772c (.base 0 (.d8 0x8)) 0x11)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x12772c (.base 0 (.d8 0x8)) 0x11).toInstrSpec (mov_m8_imm8_effect_step 0x12772c (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x11) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127730 [0x48, 0x89, 0x50, 0x0C] (StorePre 0x127730 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x127730 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127730 2 (.base 0 (.d8 0xc)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127730 2 (.base 0 (.d8 0xc))).toInstrSpec (mov_m64_r64_effect_step 0x127730 0x48 (by decide) 2 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127734 [0x48, 0x89, 0x70, 0x14] (StorePre 0x127734 4 (fun s => AddrMode.addr (.base 0 (.d8 0x14)) s (0x127734 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127734 6 (.base 0 (.d8 0x14)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127734 6 (.base 0 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x127734 0x48 (by decide) 6 (.base 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127738 [0xC3] (RetPre 0x127738) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127738).toInstrSpec (ret_effect_step 0x127738) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12772c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127730) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127734) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127738) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l127726 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127726 :=
  Rest.liftedBlock (rest_l127726 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127726 x hx)

theorem rest_l127b80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127b80 bytes_l127b80) (entryMap (live .l127b80))
      3 0x127b80 bytes_l127b80 b_l127b80 := by
  have f0 : InstrSpec 0x127b80 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x127b80) (movR64R64Effect 0x127b80 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127b80 0 7).toInstrSpec (mov_r64_r64_effect_step 0x127b80 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127b83 [0x80, 0x7E, 0x20, 0x00] (LoadPre 0x127b83 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x127b83 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x127b83 4 (.base 6 (.d8 0x20)) 0x0)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x127b83 4 (.base 6 (.d8 0x20)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x127b83 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b83) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b87) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x127b87 4 0x15) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127b80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127b80 :=
  Rest.liftedBlock (rest_l127b80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127b80 x hx)

theorem rest_l127b89 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127b89 bytes_l127b89) (entryMap (live .l127b89))
      6 0x127b89 bytes_l127b89 b_l127b89 := by
  have f0 : InstrSpec 0x127b89 [0xC6, 0x46, 0x20, 0x01] (StorePre 0x127b89 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x127b89 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127b89 (.base 6 (.d8 0x20)) 0x1)
      [.gpr 6] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127b89 (.base 6 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x127b89 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127b8d [0x8B, 0x4E, 0x1C] (LoadPre 0x127b8d (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127b8d + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127b8d 1 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x127b8d 1 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x127b8d 1 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127b90 [0xC7, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x127b90 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127b90 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127b90 6 (.base 0 .none) 0x1)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127b90 6 (.base 0 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x127b90 (.base 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127b96 [0x89, 0x48, 0x04] (StorePre 0x127b96 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127b96 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127b96 1 (.base 0 (.d8 0x4)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127b96 1 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127b96 1 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127b99 [0xC6, 0x40, 0x08, 0x02] (StorePre 0x127b99 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127b99 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127b99 (.base 0 (.d8 0x8)) 0x2)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127b99 (.base 0 (.d8 0x8)) 0x2).toInstrSpec (mov_m8_imm8_effect_step 0x127b99 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127b9d [0xC3] (RetPre 0x127b9d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127b9d).toInstrSpec (ret_effect_step 0x127b9d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b8d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b90) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b96) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b99) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127b9d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127b89 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127b89 :=
  Rest.liftedBlock (rest_l127b89 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127b89 x hx)

theorem rest_l127b9e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127b9e bytes_l127b9e) (entryMap (live .l127b9e))
      5 0x127b9e bytes_l127b9e b_l127b9e := by
  have f0 : InstrSpec 0x127b9e [0x48, 0x8B, 0x7E, 0x08] (LoadPre 0x127b9e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x127b9e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127b9e 7 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x127b9e 7 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x127b9e 0x48 (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127ba2 [0x8B, 0x4E, 0x1C] (LoadPre 0x127ba2 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127ba2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127ba2 1 (.base 6 (.d8 0x1c)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x127ba2 1 (.base 6 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x127ba2 1 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127ba5 [0x49, 0x89, 0xF9] (fun s => s.RIP = 0x127ba5) (movR64R64Effect 0x127ba5 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x127ba5 9 7).toInstrSpec (mov_r64_r64_effect_step 0x127ba5 0x49 0xf9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127ba8 [0x49, 0x29, 0xC9] (fun s => s.RIP = 0x127ba8) (subR64R64Effect 0x127ba8 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x127ba8 9 1).toInstrSpec (sub_r64_r64_effect_step 0x127ba8 0x49 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ba2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ba5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ba8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x127bab 3 0x26) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127b9e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127b9e :=
  Rest.liftedBlock (rest_l127b9e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127b9e x hx)

theorem rest_l127bad [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bad bytes_l127bad) (entryMap (live .l127bad))
      9 0x127bad bytes_l127bad b_l127bad := by
  have f0 : InstrSpec 0x127bad [0x48, 0x89, 0xF9] (fun s => s.RIP = 0x127bad) (movR64R64Effect 0x127bad 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x127bad 1 7).toInstrSpec (mov_r64_r64_effect_step 0x127bad 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127bb0 [0x48, 0xC1, 0xE1, 0x20] (fun s => s.RIP = 0x127bb0) (shlR64Effect 0x127bb0 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x127bb0 4 1 32).toInstrSpec (shl_r64_imm8_effect_step 0x127bb0 0x48 0xe1 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127bb4 [0x48, 0xBA, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127bb4) (movR64Imm64Effect 0x127bb4 2 0x100000003)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x127bb4 2 0x100000003).toInstrSpec (mov_r64_imm64_effect_step 0x127bb4 0x48 0xba (by decide) (by decide) 0x100000003) pre_rip
  have f3 : InstrSpec 0x127bbe [0x48, 0x01, 0xCA] (fun s => s.RIP = 0x127bbe) (addR64R64Effect 0x127bbe 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x127bbe 2 1).toInstrSpec (add_r64_r64_effect_step 0x127bbe 0x48 0xca (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127bc1 [0xC7, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x127bc1 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127bc1 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127bc1 6 (.base 0 .none) 0x1)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127bc1 6 (.base 0 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x127bc1 (.base 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127bc7 [0x89, 0x78, 0x04] (StorePre 0x127bc7 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127bc7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127bc7 7 (.base 0 (.d8 0x4)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127bc7 7 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127bc7 7 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127bca [0x48, 0x89, 0x50, 0x08] (StorePre 0x127bca 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127bca + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127bca 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127bca 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127bca 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x127bce [0x48, 0x89, 0x78, 0x10] (StorePre 0x127bce 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127bce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127bce 7 (.base 0 (.d8 0x10)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127bce 7 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127bce 0x48 (by decide) 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x127bd2 [0xC3] (RetPre 0x127bd2) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127bd2).toInstrSpec (ret_effect_step 0x127bd2) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bb0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bb4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bbe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bc1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bc7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bce) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bd2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 67) (ρ' := [(0, 0), (1, 55), (2, 59), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l127bad [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bad :=
  Rest.liftedBlock (rest_l127bad code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bad x hx)

theorem rest_l127bd3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bd3 bytes_l127bd3) (entryMap (live .l127bd3))
      4 0x127bd3 bytes_l127bd3 b_l127bd3 := by
  have f0 : InstrSpec 0x127bd3 [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x127bd3) (movR32R32Effect 0x127bd3 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x127bd3 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x127bd3 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127bd6 [0x01, 0xCA] (fun s => s.RIP = 0x127bd6) (addR32R32Effect 0x127bd6 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (addR32R32Effect_footprint 0x127bd6 2 2 1).toInstrSpec (add_r32_r32_effect_step 0x127bd6 0xca (by decide)) pre_rip
  have f2 : InstrSpec 0x127bd8 [0x4D, 0x39, 0xC1] (fun s => s.RIP = 0x127bd8) (cmpR64R64Effect 0x127bd8 9 8)
      [.gpr 9, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127bd8 9 8).toInstrSpec (cmp_r64_r64_effect_step 0x127bd8 0x4d 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bd6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bd8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bdb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x127bdb 3 0x1c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127bd3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bd3 :=
  Rest.liftedBlock (rest_l127bd3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bd3 x hx)

theorem rest_l127bdd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bdd bytes_l127bdd) (entryMap (live .l127bdd))
      2 0x127bdd bytes_l127bdd b_l127bdd := by
  have f0 : InstrSpec 0x127bdd [0x39, 0xCA] (fun s => s.RIP = 0x127bdd) (cmpR32R32Effect 0x127bdd 2 2 1)
      [.gpr 2, .gpr 1] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127bdd 2 2 1).toInstrSpec (cmp_r32_r32_effect_step 0x127bdd 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bdf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127bdf 2 0x55) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127bdd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bdd :=
  Rest.liftedBlock (rest_l127bdd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bdd x hx)

theorem rest_l127be1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127be1 bytes_l127be1) (entryMap (live .l127be1))
      7 0x127be1 bytes_l127be1 b_l127be1 := by
  have f0 : InstrSpec 0x127be1 [0xC6, 0x46, 0x20, 0x01] (StorePre 0x127be1 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x127be1 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127be1 (.base 6 (.d8 0x20)) 0x1)
      [.gpr 6] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127be1 (.base 6 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x127be1 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127be5 [0xC7, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x127be5 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127be5 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127be5 6 (.base 0 .none) 0x1)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127be5 6 (.base 0 .none) 0x1).toInstrSpec (mov_m32_imm32_effect_step 0x127be5 (.base 0 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127beb [0x89, 0x48, 0x04] (StorePre 0x127beb 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127beb + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127beb 1 (.base 0 (.d8 0x4)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127beb 1 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127beb 1 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127bee [0xC6, 0x40, 0x08, 0x03] (StorePre 0x127bee 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127bee + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127bee (.base 0 (.d8 0x8)) 0x3)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127bee (.base 0 (.d8 0x8)) 0x3).toInstrSpec (mov_m8_imm8_effect_step 0x127bee (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x3) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127bf2 [0x89, 0x50, 0x0C] (StorePre 0x127bf2 3 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x127bf2 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127bf2 2 (.base 0 (.d8 0xc)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127bf2 2 (.base 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x127bf2 2 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127bf5 [0x89, 0x78, 0x10] (StorePre 0x127bf5 3 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127bf5 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127bf5 7 (.base 0 (.d8 0x10)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127bf5 7 (.base 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x127bf5 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127bf8 [0xC3] (RetPre 0x127bf8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127bf8).toInstrSpec (ret_effect_step 0x127bf8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127be5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127beb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bf2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bf5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bf8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l127be1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127be1 :=
  Rest.liftedBlock (rest_l127be1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127be1 x hx)

theorem rest_l127bf9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bf9 bytes_l127bf9) (entryMap (live .l127bf9))
      2 0x127bf9 bytes_l127bf9 b_l127bf9 := by
  have f0 : InstrSpec 0x127bf9 [0x39, 0xCA] (fun s => s.RIP = 0x127bf9) (cmpR32R32Effect 0x127bf9 2 2 1)
      [.gpr 2, .gpr 1] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127bf9 2 2 1).toInstrSpec (cmp_r32_r32_effect_step 0x127bf9 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127bfb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127bfb 2 0x44) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127bf9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bf9 :=
  Rest.liftedBlock (rest_l127bf9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bf9 x hx)

theorem rest_l127bfd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127bfd bytes_l127bfd) (entryMap (live .l127bfd))
      3 0x127bfd bytes_l127bfd b_l127bfd := by
  have f0 : InstrSpec 0x127bfd [0x8B, 0x7E, 0x18] (LoadPre 0x127bfd (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x127bfd + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127bfd 7 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x127bfd 7 (.base 6 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x127bfd 7 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127c00 [0x39, 0xFA] (fun s => s.RIP = 0x127c00) (cmpR32R32Effect 0x127c00 2 2 7)
      [.gpr 2, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x127c00 2 2 7).toInstrSpec (cmp_r32_r32_effect_step 0x127c00 0xfa (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c00) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c02) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x127c02 6 0x1a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127bfd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127bfd :=
  Rest.liftedBlock (rest_l127bfd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127bfd x hx)

theorem rest_l127c04 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c04 bytes_l127c04) (entryMap (live .l127c04))
      2 0x127c04 bytes_l127c04 b_l127c04 := by
  have f0 : InstrSpec 0x127c04 [0x41, 0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127c04) (movR32Imm32Effect 0x127c04 6 8 0x1)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x127c04 6 8 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x127c04 0x41 0xb8 (by decide) (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x127c0a [0x40, 0xB6, 0x03] (fun s => s.RIP = 0x127c0a) (movR8Imm8Effect 0x127c0a 3 6 0x3)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR8Imm8Effect_footprint 0x127c0a 3 6 0x3).toInstrSpec (mov_r8_imm8_rex_effect_step 0x127c0a 0x40 (by decide) 0xb6 (by decide) 0x3) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c0a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c0d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l127c04 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c04 :=
  Rest.liftedBlock (rest_l127c04 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c04 x hx)

theorem rest_l127c0d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c0d bytes_l127c0d) (entryMap (live .l127c0d))
      6 0x127c0d bytes_l127c0d b_l127c0d := by
  have f0 : InstrSpec 0x127c0d [0x44, 0x89, 0x00] (StorePre 0x127c0d 3 (fun s => AddrMode.addr (.base 0 .none) s (0x127c0d + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x127c0d 8 (.base 0 .none))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM32R32Effect_footprint 0x127c0d 8 (.base 0 .none)).toInstrSpec (mov_m32_r32_effect_step 0x127c0d 0x44 (by decide) 0 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127c10 [0x89, 0x48, 0x04] (StorePre 0x127c10 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127c10 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c10 1 (.base 0 (.d8 0x4)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c10 1 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c10 1 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127c13 [0x40, 0x88, 0x70, 0x08] (StorePre 0x127c13 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c13 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127c13 4 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x127c13 4 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x127c13 0x40 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127c17 [0x89, 0x50, 0x0C] (StorePre 0x127c17 3 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x127c17 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c17 2 (.base 0 (.d8 0xc)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c17 2 (.base 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c17 2 (.base 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127c1a [0x89, 0x78, 0x10] (StorePre 0x127c1a 3 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127c1a + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c1a 7 (.base 0 (.d8 0x10)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c1a 7 (.base 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c1a 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127c1d [0xC3] (RetPre 0x127c1d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127c1d).toInstrSpec (ret_effect_step 0x127c1d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c10) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c13) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c17) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c1a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c1d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127c0d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c0d :=
  Rest.liftedBlock (rest_l127c0d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c0d x hx)

theorem rest_l127c1e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c1e bytes_l127c1e) (entryMap (live .l127c1e))
      7 0x127c1e bytes_l127c1e b_l127c1e := by
  have f0 : InstrSpec 0x127c1e [0x48, 0x8B, 0x3E] (LoadPre 0x127c1e (fun s => AddrMode.addr (.base 6 .none) s (0x127c1e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x127c1e 7 (.base 6 .none))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x127c1e 7 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x127c1e 0x48 (by decide) 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127c21 [0x48, 0x01, 0xCF] (fun s => s.RIP = 0x127c21) (addR64R64Effect 0x127c21 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x127c21 7 1).toInstrSpec (add_r64_r64_effect_step 0x127c21 0x48 0xcf (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127c24 [0x89, 0x56, 0x1C] (StorePre 0x127c24 3 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127c24 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c24 2 (.base 6 (.d8 0x1c)))
      [.gpr 2, .gpr 6] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c24 2 (.base 6 (.d8 0x1c))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c24 2 (.base 6 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127c27 [0x48, 0x89, 0x78, 0x08] (StorePre 0x127c27 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c27 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c27 7 (.base 0 (.d8 0x8)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127c27 7 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127c27 0x48 (by decide) 7 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x127c2b [0x4C, 0x89, 0x40, 0x10] (StorePre 0x127c2b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127c2b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c2b 8 (.base 0 (.d8 0x10)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127c2b 8 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127c2b 0x4c (by decide) 0 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127c2f [0xC7, 0x00, 0x02, 0x00, 0x00, 0x00] (StorePre 0x127c2f 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127c2f + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127c2f 6 (.base 0 .none) 0x2)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127c2f 6 (.base 0 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x127c2f (.base 0 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x127c35 [0xC3] (RetPre 0x127c35) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127c35).toInstrSpec (ret_effect_step 0x127c35) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c21) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c24) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c27) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c2b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c2f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c35) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 62), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l127c1e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c1e :=
  Rest.liftedBlock (rest_l127c1e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c1e x hx)

theorem rest_l127c36 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c36 bytes_l127c36) (entryMap (live .l127c36))
      3 0x127c36 bytes_l127c36 b_l127c36 := by
  have f0 : InstrSpec 0x127c36 [0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x127c36 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127c36 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127c36 6 (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x127c36 6 (.base 0 .none) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x127c36 (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127c3c [0xC6, 0x40, 0x08, 0x0C] (StorePre 0x127c3c 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c3c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127c3c (.base 0 (.d8 0x8)) 0xc)
      [.gpr 0] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x127c3c (.base 0 (.d8 0x8)) 0xc).toInstrSpec (mov_m8_imm8_effect_step 0x127c3c (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0xc) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127c40 [0xC3] (RetPre 0x127c40) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127c40).toInstrSpec (ret_effect_step 0x127c40) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c3c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c40) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l127c36 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c36 :=
  Rest.liftedBlock (rest_l127c36 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c36 x hx)

theorem rest_l127c41 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c41 bytes_l127c41) (entryMap (live .l127c41))
      3 0x127c41 bytes_l127c41 b_l127c41 := by
  have f0 : InstrSpec 0x127c41 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x127c41) (xorR32R32Effect 0x127c41 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127c41 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x127c41 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127c44 [0x40, 0xB6, 0x0C] (fun s => s.RIP = 0x127c44) (movR8Imm8Effect 0x127c44 3 6 0xc)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR8Imm8Effect_footprint 0x127c44 3 6 0xc).toInstrSpec (mov_r8_imm8_rex_effect_step 0x127c44 0x40 (by decide) 0xb6 (by decide) 0xc) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c44) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c47) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x127c47 0xc4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127c41 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c41 :=
  Rest.liftedBlock (rest_l127c41 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c41 x hx)

theorem rest_l127c50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c50 bytes_l127c50) (entryMap (live .l127c50))
      5 0x127c50 bytes_l127c50 b_l127c50 := by
  have f0 : InstrSpec 0x127c50 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x127c50) (movR64R64Effect 0x127c50 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127c50 0 7).toInstrSpec (mov_r64_r64_effect_step 0x127c50 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127c53 [0x89, 0xC9] (fun s => s.RIP = 0x127c53) (movR32R32Effect 0x127c53 2 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x127c53 2 1 1).toInstrSpec (mov_r32_r32_effect_step 0x127c53 0xc9 (by decide)) pre_rip
  have f2 : InstrSpec 0x127c55 [0xBF, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127c55) (movR32Imm32Effect 0x127c55 5 7 0x2)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x127c55 5 7 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x127c55 0xbf (by decide) 0x2) pre_rip
  have f3 : InstrSpec 0x127c5a [0x48, 0x39, 0xCA] (fun s => s.RIP = 0x127c5a) (cmpR64R64Effect 0x127c5a 2 1)
      [.gpr 2, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127c5a 2 1).toInstrSpec (cmp_r64_r64_effect_step 0x127c5a 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c55) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c5a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c5d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x127c5d 3 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127c50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c50 :=
  Rest.liftedBlock (rest_l127c50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c50 x hx)

theorem rest_l127c5f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c5f bytes_l127c5f) (entryMap (live .l127c5f))
      7 0x127c5f bytes_l127c5f b_l127c5f := by
  have f0 : InstrSpec 0x127c5f [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x127c5f) (movR64R64Effect 0x127c5f 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x127c5f 1 2).toInstrSpec (mov_r64_r64_effect_step 0x127c5f 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127c62 [0x48, 0xC1, 0xE1, 0x20] (fun s => s.RIP = 0x127c62) (shlR64Effect 0x127c62 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x127c62 4 1 32).toInstrSpec (shl_r64_imm8_effect_step 0x127c62 0x48 0xe1 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127c66 [0x48, 0xBE, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127c66) (movR64Imm64Effect 0x127c66 6 0x100000003)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x127c66 6 0x100000003).toInstrSpec (mov_r64_imm64_effect_step 0x127c66 0x48 0xbe (by decide) (by decide) 0x100000003) pre_rip
  have f3 : InstrSpec 0x127c70 [0x48, 0x01, 0xCE] (fun s => s.RIP = 0x127c70) (addR64R64Effect 0x127c70 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x127c70 6 1).toInstrSpec (add_r64_r64_effect_step 0x127c70 0x48 0xce (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127c73 [0x89, 0x50, 0x04] (StorePre 0x127c73 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127c73 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c73 2 (.base 0 (.d8 0x4)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c73 2 (.base 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x127c73 2 (.base 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x127c76 [0xBF, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127c76) (movR32Imm32Effect 0x127c76 5 7 0x1)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x127c76 5 7 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x127c76 0xbf (by decide) 0x1) pre_rip
  have f6 : InstrSpec 0x127c7b [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x127c7b) (movR64R64Effect 0x127c7b 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x127c7b 1 2).toInstrSpec (mov_r64_r64_effect_step 0x127c7b 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c62) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c66) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c70) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c73) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c76) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c7b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c7e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 66) (by decide) rfl

theorem block_l127c5f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c5f :=
  Rest.liftedBlock (rest_l127c5f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c5f x hx)

theorem rest_l127c7e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127c7e bytes_l127c7e) (entryMap (live .l127c7e))
      4 0x127c7e bytes_l127c7e b_l127c7e := by
  have f0 : InstrSpec 0x127c7e [0x89, 0x38] (StorePre 0x127c7e 2 (fun s => AddrMode.addr (.base 0 .none) s (0x127c7e + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x127c7e 7 (.base 0 .none))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x127c7e 7 (.base 0 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x127c7e 7 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x127c80 [0x48, 0x89, 0x70, 0x08] (StorePre 0x127c80 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c80 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c80 6 (.base 0 (.d8 0x8)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127c80 6 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x127c80 0x48 (by decide) 6 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127c84 [0x48, 0x89, 0x48, 0x10] (StorePre 0x127c84 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127c84 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c84 1 (.base 0 (.d8 0x10)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x127c84 1 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x127c84 0x48 (by decide) 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x127c88 [0xC3] (RetPre 0x127c88) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127c88).toInstrSpec (ret_effect_step 0x127c88) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c80) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c84) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127c88) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l127c7e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127c7e :=
  Rest.liftedBlock (rest_l127c7e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127c7e x hx)

theorem rest_l127d50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127d50 bytes_l127d50) (entryMap (live .l127d50))
      5 0x127d50 bytes_l127d50 b_l127d50 := by
  have f0 : InstrSpec 0x127d50 [0x48, 0x83, 0xEC, 0x01] (fun s => s.RIP = 0x127d50) (subR64Imm8Effect 0x127d50 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x127d50 4 0x1).toInstrSpec (sub_r64_imm8_effect_step 0x127d50 0x48 0xec 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127d54 [0x40, 0x88, 0x3C, 0x24] (StorePre 0x127d54 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127d54 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127d54 4 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x127d54 4 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x127d54 0x40 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x127d58 [0x0F, 0xB6, 0x04, 0x24] (LoadPre 0x127d58 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127d58 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x127d58 4 0 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x127d58 4 0 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x127d58 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x127d5c [0x48, 0x83, 0xC4, 0x01] (fun s => s.RIP = 0x127d5c) (addR64Imm8Effect 0x127d5c 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x127d5c 4 0x1).toInstrSpec (add_r64_imm8_effect_step 0x127d5c 0x48 0xc4 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127d60 [0xC3] (RetPre 0x127d60) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127d60).toInstrSpec (ret_effect_step 0x127d60) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d54) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d58) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d60) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 62) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l127d50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127d50 :=
  Rest.liftedBlock (rest_l127d50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127d50 x hx)

theorem rest_l128a40 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a40 bytes_l128a40) (entryMap (live .l128a40))
      4 0x128a40 bytes_l128a40 b_l128a40 := by
  have f0 : InstrSpec 0x128a40 [0x48, 0x8B, 0x17] (LoadPre 0x128a40 (fun s => AddrMode.addr (.base 7 .none) s (0x128a40 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128a40 2 (.base 7 .none))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x128a40 2 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128a40 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128a43 [0x0F, 0xB6, 0x4F, 0x10] (LoadPre 0x128a43 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128a43 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x128a43 4 1 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x128a43 4 1 (.base 7 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x128a43 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128a47 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x128a47) (testR64R64Effect 0x128a47 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128a47 2 2).toInstrSpec (test_r64_r64_effect_step 0x128a47 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a43) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a47) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a4a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x128a4a 4 0x72) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a40 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a40 :=
  Rest.liftedBlock (rest_l128a40 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a40 x hx)

theorem rest_l128a4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a4c bytes_l128a4c) (entryMap (live .l128a4c))
      3 0x128a4c bytes_l128a4c b_l128a4c := by
  have f0 : InstrSpec 0x128a4c [0xB0, 0x01] (fun s => s.RIP = 0x128a4c) (movR8Imm8Effect 0x128a4c 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128a4c 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128a4c 0xb0 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x128a4e [0x84, 0xC9] (fun s => s.RIP = 0x128a4e) (testR8R8Effect 0x128a4e 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128a4e 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x128a4e 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a4e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a50) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x128a50 5 0x67) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a4c :=
  Rest.liftedBlock (rest_l128a4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a4c x hx)

theorem rest_l128a52 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a52 bytes_l128a52) (entryMap (live .l128a52))
      7 0x128a52 bytes_l128a52 b_l128a52 := by
  have f0 : InstrSpec 0x128a52 [0x55] (PushPre 0x128a52 1) (pushR64Effect 0x128a52 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128a52 1 5).toInstrSpec (push_r64_effect_step 0x128a52 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128a53 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x128a53) (movR64R64Effect 0x128a53 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x128a53 5 4).toInstrSpec (mov_r64_r64_effect_step 0x128a53 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128a56 [0x41, 0x56] (PushPre 0x128a56 2) (pushR64Effect 0x128a56 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128a56 2 14).toInstrSpec (push_r64_rex_effect_step 0x128a56 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128a58 [0x53] (PushPre 0x128a58 1) (pushR64Effect 0x128a58 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128a58 1 3).toInstrSpec (push_r64_effect_step 0x128a58 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128a59 [0x48, 0x8B, 0x5F, 0x08] (LoadPre 0x128a59 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x128a59 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a59 3 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x128a59 3 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128a59 0x48 (by decide) 3 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x128a5d [0x48, 0x83, 0xFA, 0x01] (fun s => s.RIP = 0x128a5d) (cmpR64Imm8Effect 0x128a5d 2 0x1)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x128a5d 2 0x1).toInstrSpec (cmp_r64_imm8_effect_step 0x128a5d 0x48 0xfa 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (7, 7), (14, 14)]) (p' := 0x128a53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 53), (7, 7), (14, 14)]) (p' := 0x128a56) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 56), (7, 7), (14, 14)]) (p' := 0x128a58) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (7, 7), (14, 14)]) (p' := 0x128a59) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 59), (7, 7), (14, 14)]) (p' := 0x128a5d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 59), (7, 7), (14, 14), (19, 61)]) (p' := 0x128a61) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x128a61 5 0x33) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a52 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a52 :=
  Rest.liftedBlock (rest_l128a52 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a52 x hx)

theorem rest_l128a63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a63 bytes_l128a63) (entryMap (live .l128a63))
      2 0x128a63 bytes_l128a63 b_l128a63 := by
  have f0 : InstrSpec 0x128a63 [0x80, 0x7F, 0x11, 0x00] (LoadPre 0x128a63 (fun s => AddrMode.addr (.base 7 (.d8 0x11)) s (0x128a63 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x128a63 4 (.base 7 (.d8 0x11)) 0x0)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x128a63 4 (.base 7 (.d8 0x11)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x128a63 (.base 7 (.d8 0x11)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (7, 7), (19, 53)]) (p' := 0x128a67) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128a67 4 0x2d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a63 :=
  Rest.liftedBlock (rest_l128a63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a63 x hx)

theorem rest_l128a69 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a69 bytes_l128a69) (entryMap (live .l128a69))
      2 0x128a69 bytes_l128a69 b_l128a69 := by
  have f0 : InstrSpec 0x128a69 [0xF6, 0x43, 0x12, 0x80] (LoadPre 0x128a69 (fun s => AddrMode.addr (.base 3 (.d8 0x12)) s (0x128a69 + BitVec.ofNat 64 4)) 1) (testM8Imm8Effect 0x128a69 4 (.base 3 (.d8 0x12)) 0x80)
      [.gpr 3] [] [.flags, .rip] :=
    (testM8Imm8Effect_footprint 0x128a69 4 (.base 3 (.d8 0x12)) 0x80).toInstrSpec (test_m8_imm8_effect_step 0x128a69 (.base 3 (.d8 0x12)) (by decide) (by decide) (by decide) 0x80) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (7, 7), (19, 53)]) (p' := 0x128a6d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128a6d 5 0x27) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a69 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a69 :=
  Rest.liftedBlock (rest_l128a69 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a69 x hx)

theorem rest_l128a6f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a6f bytes_l128a6f) (entryMap (live .l128a6f))
      6 0x128a6f bytes_l128a6f b_l128a6f := by
  have f0 : InstrSpec 0x128a6f [0x48, 0x8B, 0x03] (LoadPre 0x128a6f (fun s => AddrMode.addr (.base 3 .none) s (0x128a6f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128a6f 0 (.base 3 .none))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128a6f 0 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128a6f 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128a72 [0x48, 0x8B, 0x4B, 0x08] (LoadPre 0x128a72 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x128a72 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a72 1 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x128a72 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128a72 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128a76 [0x48, 0x8D, 0x35, 0xB8, 0xB1, 0x0D, 0x00] (fun s => s.RIP = 0x128a76) (leaR64Effect 0x128a76 6 (.rip 0xdb1b8))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128a76 6 (.rip 0xdb1b8)).toInstrSpec (lea_r64_effect_step 0x128a76 0x48 (by decide) 6 (.rip 0xdb1b8) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128a7d [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128a7d) (movR32Imm32Effect 0x128a7d 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128a7d 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x128a7d 0xba (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x128a82 [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x128a82) (movR64R64Effect 0x128a82 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x128a82 14 7).toInstrSpec (mov_r64_r64_effect_step 0x128a82 0x49 0xfe (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x128a85 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x128a85) (movR64R64Effect 0x128a85 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128a85 7 0).toInstrSpec (mov_r64_r64_effect_step 0x128a85 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a72) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a76) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a7d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a82) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a85) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (3, 3)]) (p' := 0x128a88) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128a6f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a6f :=
  Rest.liftedBlock (rest_l128a6f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a6f x hx)

theorem rest_l128a8b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a8b bytes_l128a8b) (entryMap (live .l128a8b))
      5 0x128a8b bytes_l128a8b b_l128a8b := by
  have f0 : InstrSpec 0x128a8b [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x128a8b) (movR64R64Effect 0x128a8b 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128a8b 7 14).toInstrSpec (mov_r64_r64_effect_step 0x128a8b 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128a8e [0x89, 0xC1] (fun s => s.RIP = 0x128a8e) (movR32R32Effect 0x128a8e 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x128a8e 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x128a8e 0xc1 (by decide)) pre_rip
  have f2 : InstrSpec 0x128a90 [0xB0, 0x01] (fun s => s.RIP = 0x128a90) (movR8Imm8Effect 0x128a90 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128a90 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128a90 0xb0 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x128a92 [0x84, 0xC9] (fun s => s.RIP = 0x128a92) (testR8R8Effect 0x128a92 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128a92 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x128a92 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a8e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a90) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a92) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a94) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x128a94 5 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a8b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a8b :=
  Rest.liftedBlock (rest_l128a8b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a8b x hx)

theorem rest_l128a96 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a96 bytes_l128a96) (entryMap (live .l128a96))
      6 0x128a96 bytes_l128a96 b_l128a96 := by
  have f0 : InstrSpec 0x128a96 [0x48, 0x8B, 0x03] (LoadPre 0x128a96 (fun s => AddrMode.addr (.base 3 .none) s (0x128a96 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128a96 0 (.base 3 .none))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128a96 0 (.base 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128a96 0x48 (by decide) 0 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128a99 [0x48, 0x8B, 0x4B, 0x08] (LoadPre 0x128a99 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x128a99 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a99 1 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x128a99 1 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128a99 0x48 (by decide) 1 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128a9d [0x48, 0x8D, 0x35, 0x90, 0xB1, 0x0D, 0x00] (fun s => s.RIP = 0x128a9d) (leaR64Effect 0x128a9d 6 (.rip 0xdb190))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128a9d 6 (.rip 0xdb190)).toInstrSpec (lea_r64_effect_step 0x128a9d 0x48 (by decide) 6 (.rip 0xdb190) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128aa4 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128aa4) (movR32Imm32Effect 0x128aa4 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128aa4 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x128aa4 0xba (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x128aa9 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x128aa9) (movR64R64Effect 0x128aa9 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x128aa9 3 7).toInstrSpec (mov_r64_r64_effect_step 0x128aa9 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x128aac [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x128aac) (movR64R64Effect 0x128aac 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128aac 7 0).toInstrSpec (mov_r64_r64_effect_step 0x128aac 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a99) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128a9d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128aa4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (3, 3), (7, 7)]) (p' := 0x128aa9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (7, 7)]) (p' := 0x128aac) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53)]) (p' := 0x128aaf) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128a96 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a96 :=
  Rest.liftedBlock (rest_l128a96 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a96 x hx)

theorem rest_l128ab2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ab2 bytes_l128ab2) (entryMap (live .l128ab2))
      1 0x128ab2 bytes_l128ab2 b_l128ab2 := by
  have f0 : InstrSpec 0x128ab2 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x128ab2) (movR64R64Effect 0x128ab2 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128ab2 7 3).toInstrSpec (mov_r64_r64_effect_step 0x128ab2 0x48 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ab5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l128ab2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ab2 :=
  Rest.liftedBlock (rest_l128ab2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ab2 x hx)

theorem rest_l128ab5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ab5 bytes_l128ab5) (entryMap (live .l128ab5))
      3 0x128ab5 bytes_l128ab5 b_l128ab5 := by
  have f0 : InstrSpec 0x128ab5 [0x5B] (PopPre 0x128ab5) (popR64Effect 0x128ab5 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128ab5 1 3).toInstrSpec (pop_r64_effect_step 0x128ab5 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128ab6 [0x41, 0x5E] (PopPre 0x128ab6) (popR64Effect 0x128ab6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128ab6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x128ab6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x128ab8 [0x5D] (PopPre 0x128ab8) (popR64Effect 0x128ab8 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128ab8 1 5).toInstrSpec (pop_r64_effect_step 0x128ab8 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (2, 2), (3, 53), (4, 54), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ab6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (3, 53), (4, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ab8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (2, 2), (3, 53), (4, 60), (5, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ab9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l128ab5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ab5 :=
  Rest.liftedBlock (rest_l128ab5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ab5 x hx)

theorem rest_l128ab9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ab9 bytes_l128ab9) (entryMap (live .l128ab9))
      2 0x128ab9 bytes_l128ab9 b_l128ab9 := by
  have f0 : InstrSpec 0x128ab9 [0x88, 0x47, 0x10] (StorePre 0x128ab9 3 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128ab9 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x128ab9 3 0 (.base 7 (.d8 0x10)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x128ab9 3 0 (.base 7 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x128ab9 0 (by decide) (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x128abc [0x89, 0xC1] (fun s => s.RIP = 0x128abc) (movR32R32Effect 0x128abc 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x128abc 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x128abc 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128abc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128abe) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l128ab9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ab9 :=
  Rest.liftedBlock (rest_l128ab9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ab9 x hx)

theorem rest_l128abe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128abe bytes_l128abe) (entryMap (live .l128abe))
      2 0x128abe bytes_l128abe b_l128abe := by
  have f0 : InstrSpec 0x128abe [0x89, 0xC8] (fun s => s.RIP = 0x128abe) (movR32R32Effect 0x128abe 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x128abe 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x128abe 0xc8 (by decide)) pre_rip
  have f1 : InstrSpec 0x128ac0 [0xC3] (RetPre 0x128ac0) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128ac0).toInstrSpec (ret_effect_step 0x128ac0) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128ac0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l128abe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128abe :=
  Rest.liftedBlock (rest_l128abe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128abe x hx)

theorem rest_l128ad0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128ad0 bytes_l128ad0) (entryMap (live .l128ad0))
      13 0x128ad0 bytes_l128ad0 b_l128ad0 := by
  have f0 : InstrSpec 0x128ad0 [0x55] (PushPre 0x128ad0 1) (pushR64Effect 0x128ad0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad0 1 5).toInstrSpec (push_r64_effect_step 0x128ad0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128ad1 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x128ad1) (movR64R64Effect 0x128ad1 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x128ad1 5 4).toInstrSpec (mov_r64_r64_effect_step 0x128ad1 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128ad4 [0x41, 0x57] (PushPre 0x128ad4 2) (pushR64Effect 0x128ad4 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad4 2 15).toInstrSpec (push_r64_rex_effect_step 0x128ad4 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128ad6 [0x41, 0x56] (PushPre 0x128ad6 2) (pushR64Effect 0x128ad6 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad6 2 14).toInstrSpec (push_r64_rex_effect_step 0x128ad6 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128ad8 [0x53] (PushPre 0x128ad8 1) (pushR64Effect 0x128ad8 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad8 1 3).toInstrSpec (push_r64_effect_step 0x128ad8 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x128ad9 [0x50] (PushPre 0x128ad9 1) (pushR64Effect 0x128ad9 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128ad9 1 0).toInstrSpec (push_r64_effect_step 0x128ad9 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x128ada [0x48, 0x89, 0xCB] (fun s => s.RIP = 0x128ada) (movR64R64Effect 0x128ada 3 1)
      [.gpr 1] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x128ada 3 1).toInstrSpec (mov_r64_r64_effect_step 0x128ada 0x48 0xcb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x128add [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x128add) (movR64R64Effect 0x128add 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x128add 14 6).toInstrSpec (mov_r64_r64_effect_step 0x128add 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x128ae0 [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x128ae0) (movR64R64Effect 0x128ae0 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x128ae0 15 7).toInstrSpec (mov_r64_r64_effect_step 0x128ae0 0x49 0xff (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x128ae3 [0x48, 0x8B, 0x3E] (LoadPre 0x128ae3 (fun s => AddrMode.addr (.base 6 .none) s (0x128ae3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128ae3 7 (.base 6 .none))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128ae3 7 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128ae3 0x48 (by decide) 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x128ae6 [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x128ae6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x128ae6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128ae6 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128ae6 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128ae6 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x128aea [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x128aea) (movR64R64Effect 0x128aea 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128aea 6 2).toInstrSpec (mov_r64_r64_effect_step 0x128aea 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x128aed [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x128aed) (movR64R64Effect 0x128aed 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x128aed 2 1).toInstrSpec (mov_r64_r64_effect_step 0x128aed 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ad9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128ada) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (6, 6), (7, 7), (14, 14), (15, 15)]) (p' := 0x128add) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (6, 6), (7, 7), (15, 15)]) (p' := 0x128ae0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (6, 6), (7, 7)]) (p' := 0x128ae3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (6, 6)]) (p' := 0x128ae6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (6, 6)]) (p' := 0x128aea) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2)]) (p' := 0x128aed) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 1)]) (p' := 0x128af0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128ad0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128ad0 :=
  Rest.liftedBlock (rest_l128ad0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128ad0 x hx)

theorem rest_l128af3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128af3 bytes_l128af3) (entryMap (live .l128af3))
      12 0x128af3 bytes_l128af3 b_l128af3 := by
  have f0 : InstrSpec 0x128af3 [0x48, 0x85, 0xDB] (fun s => s.RIP = 0x128af3) (testR64R64Effect 0x128af3 3 3)
      [.gpr 3, .gpr 3] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128af3 3 3).toInstrSpec (test_r64_r64_effect_step 0x128af3 0x48 0xdb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128af6 [0x4D, 0x89, 0x77, 0x08] (StorePre 0x128af6 4 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x128af6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128af6 14 (.base 15 (.d8 0x8)))
      [.gpr 14, .gpr 15] [] [.rip] :=
    (movM64R64Effect_footprint 0x128af6 14 (.base 15 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x128af6 0x4d (by decide) 6 (.base 15 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x128afa [0x41, 0x88, 0x47, 0x10] (StorePre 0x128afa 4 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x128afa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x128afa 4 0 (.base 15 (.d8 0x10)))
      [.gpr 0, .gpr 15] [] [.rip] :=
    (movM8R8Effect_footprint 0x128afa 4 0 (.base 15 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x128afa 0x41 (by decide) 0 (.base 15 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x128afe [0x49, 0xC7, 0x07, 0x00, 0x00, 0x00, 0x00] (StorePre 0x128afe 7 (fun s => AddrMode.addr (.base 15 .none) s (0x128afe + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x128afe (.base 15 .none) 0x0)
      [.gpr 15] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x128afe (.base 15 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x128afe 0x49 (by decide) (.base 15 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x128b05 [0x41, 0x0F, 0x94, 0x47, 0x11] (StorePre 0x128b05 5 (fun s => AddrMode.addr (.base 15 (.d8 0x11)) s (0x128b05 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x128b05 5 (.base 15 (.d8 0x11))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 15] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x128b05 5 (.base 15 (.d8 0x11)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_rex_effect_step 0x128b05 4 0x41 (by decide) 0 (.base 15 (.d8 0x11)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x128b0a [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x128b0a) (movR64R64Effect 0x128b0a 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x128b0a 0 15).toInstrSpec (mov_r64_r64_effect_step 0x128b0a 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x128b0d [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x128b0d) (addR64Imm8Effect 0x128b0d 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x128b0d 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x128b0d 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x128b11 [0x5B] (PopPre 0x128b11) (popR64Effect 0x128b11 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128b11 1 3).toInstrSpec (pop_r64_effect_step 0x128b11 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x128b12 [0x41, 0x5E] (PopPre 0x128b12) (popR64Effect 0x128b12 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128b12 2 14).toInstrSpec (pop_r64_rex_effect_step 0x128b12 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x128b14 [0x41, 0x5F] (PopPre 0x128b14) (popR64Effect 0x128b14 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128b14 2 15).toInstrSpec (pop_r64_rex_effect_step 0x128b14 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x128b16 [0x5D] (PopPre 0x128b16) (popR64Effect 0x128b16 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128b16 1 5).toInstrSpec (pop_r64_effect_step 0x128b16 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x128b17 [0xC3] (RetPre 0x128b17) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128b17).toInstrSpec (ret_effect_step 0x128b17) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128af6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128afa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128afe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b05) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b0a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b0d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b11) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b12) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b14) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b16) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b17) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 63), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f11 (by decide) rfl rfl rfl (by decide)

theorem block_l128af3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128af3 :=
  Rest.liftedBlock (rest_l128af3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128af3 x hx)

theorem rest_l129560 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129560 bytes_l129560) (entryMap (live .l129560))
      12 0x129560 bytes_l129560 b_l129560 := by
  have f0 : InstrSpec 0x129560 [0x55] (PushPre 0x129560 1) (pushR64Effect 0x129560 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129560 1 5).toInstrSpec (push_r64_effect_step 0x129560 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129561 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129561) (movR64R64Effect 0x129561 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129561 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129561 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129564 [0x48, 0x83, 0xEC, 0x20] (fun s => s.RIP = 0x129564) (subR64Imm8Effect 0x129564 4 0x20)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129564 4 0x20).toInstrSpec (sub_r64_imm8_effect_step 0x129564 0x48 0xec 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129568 [0x48, 0x89, 0x7D, 0xF0] (StorePre 0x129568 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129568 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129568 7 (.base 5 (.d8 0xf0)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129568 7 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129568 0x48 (by decide) 7 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12956c [0x48, 0x89, 0x75, 0xF8] (StorePre 0x12956c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12956c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12956c 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12956c 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x12956c 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129570 [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x129570) (leaR64Effect 0x129570 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129570 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129570 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129574 [0x48, 0x89, 0x45, 0xE0] (StorePre 0x129574 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129574 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129574 0 (.base 5 (.d8 0xe0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129574 0 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129574 0x48 (by decide) 0 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129578 [0x48, 0x8D, 0x05, 0xF1, 0x0A, 0x00, 0x00] (fun s => s.RIP = 0x129578) (leaR64Effect 0x129578 0 (.rip 0xaf1))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129578 0 (.rip 0xaf1)).toInstrSpec (lea_r64_effect_step 0x129578 0x48 (by decide) 0 (.rip 0xaf1) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12957f [0x48, 0x89, 0x45, 0xE8] (StorePre 0x12957f 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12957f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12957f 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12957f 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x12957f 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129583 [0x48, 0x8D, 0x3D, 0x81, 0x84, 0x0D, 0x00] (fun s => s.RIP = 0x129583) (leaR64Effect 0x129583 7 (.rip 0xd8481))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129583 7 (.rip 0xd8481)).toInstrSpec (lea_r64_effect_step 0x129583 0x48 (by decide) 7 (.rip 0xd8481) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12958a [0x48, 0x8D, 0x75, 0xE0] (fun s => s.RIP = 0x12958a) (leaR64Effect 0x12958a 6 (.base 5 (.d8 0xe0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x12958a 6 (.base 5 (.d8 0xe0))).toInstrSpec (lea_r64_effect_step 0x12958a 0x48 (by decide) 6 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12958e [0xFF, 0x15, 0x4C, 0xA8, 0x0D, 0x00] (GoesTo (CallMemPre 0x12958e (.rip 0xda84c)) (callEffect (callMemPtr 0x12958e (.rip 0xda84c)) (0x12958e + BitVec.ofNat 64 (callMemLen (.rip 0xda84c)))) 0x129770) (callEffect (callMemPtr 0x12958e (.rip 0xda84c)) (0x12958e + BitVec.ofNat 64 (callMemLen (.rip 0xda84c))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12958e (.rip 0xda84c)).toInstrSpec (call_m64_effect_step 0x12958e (.rip 0xda84c) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129561) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129564) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129568) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12956c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129570) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129574) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129578) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12957f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129583) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 67)]) (p' := 0x12958a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 69), (7, 67)]) (p' := 0x12958e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (2, 2), (4, 71), (5, 55), (6, 69), (7, 67)]) (p' := 0x129770) f11 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l129560 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129560 :=
  Rest.liftedBlock (rest_l129560 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129560 x hx)

theorem rest_l129594 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129594 bytes_l129594) (entryMap (live .l129594))
      2 0x129594 bytes_l129594 b_l129594 := by
  have f0 : InstrSpec 0x129594 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129594) (fun _ => nopEffect 0x129594 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x129594 10).toInstrSpec (nop_m_effect_step 0x129594 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12959e [0x66, 0x90] (fun s => s.RIP = 0x12959e) (fun _ => nopEffect 0x12959e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12959e 2).toInstrSpec (nop_66_effect_step 0x12959e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)]) (p' := 0x12959e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)]) (p' := 0x1295a0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l129594 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129594 :=
  Rest.liftedBlock (rest_l129594 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129594 x hx)

theorem rest_l129770 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129770 bytes_l129770) (entryMap (live .l129770))
      11 0x129770 bytes_l129770 b_l129770 := by
  have f0 : InstrSpec 0x129770 [0x55] (PushPre 0x129770 1) (pushR64Effect 0x129770 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129770 1 5).toInstrSpec (push_r64_effect_step 0x129770 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129771 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129771) (movR64R64Effect 0x129771 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129771 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129771 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129774 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x129774) (subR64Imm8Effect 0x129774 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129774 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x129774 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129778 [0x48, 0x89, 0x7D, 0xF0] (StorePre 0x129778 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129778 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129778 7 (.base 5 (.d8 0xf0)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129778 7 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129778 0x48 (by decide) 7 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x12977c [0x48, 0x89, 0x75, 0xF8] (StorePre 0x12977c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12977c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12977c 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x12977c 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x12977c 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129780 [0x48, 0x8D, 0x45, 0xF0] (fun s => s.RIP = 0x129780) (leaR64Effect 0x129780 0 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129780 0 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129780 0x48 (by decide) 0 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129784 [0x48, 0x89, 0x45, 0xD8] (StorePre 0x129784 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129784 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129784 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129784 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129784 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129788 [0x48, 0x89, 0x55, 0xE0] (StorePre 0x129788 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129788 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129788 2 (.base 5 (.d8 0xe0)))
      [.gpr 2, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129788 2 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129788 0x48 (by decide) 2 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12978c [0x66, 0xC7, 0x45, 0xE8, 0x01, 0x00] (StorePre 0x12978c 6 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12978c + BitVec.ofNat 64 6)) 2) (movM16Imm16Effect 0x12978c (.base 5 (.d8 0xe8)) 0x1)
      [.gpr 5] [] [.rip] :=
    (movM16Imm16Effect_footprint 0x12978c (.base 5 (.d8 0xe8)) 0x1).toInstrSpec (mov_m16_imm16_effect_step 0x12978c (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129792 [0x48, 0x8D, 0x7D, 0xD8] (fun s => s.RIP = 0x129792) (leaR64Effect 0x129792 7 (.base 5 (.d8 0xd8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129792 7 (.base 5 (.d8 0xd8))).toInstrSpec (lea_r64_effect_step 0x129792 0x48 (by decide) 7 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129796 [0xFF, 0x15, 0x84, 0xA6, 0x0D, 0x00] (GoesTo (CallMemPre 0x129796 (.rip 0xda684)) (callEffect (callMemPtr 0x129796 (.rip 0xda684)) (0x129796 + BitVec.ofNat 64 (callMemLen (.rip 0xda684)))) 0x100a20) (callEffect (callMemPtr 0x129796 (.rip 0xda684)) (0x129796 + BitVec.ofNat 64 (callMemLen (.rip 0xda684))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129796 (.rip 0xda684)).toInstrSpec (call_m64_effect_step 0x129796 (.rip 0xda684) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x100a20
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129771) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129774) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129778) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12977c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129780) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129784) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129788) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x12978c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129792) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6)]) (p' := 0x129796) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 61), (2, 2), (5, 55), (6, 6)]) (p' := 0x100a20) f10 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l129770 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129770 :=
  Rest.liftedBlock (rest_l129770 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129770 x hx)

theorem rest_l12979c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12979c bytes_l12979c) (entryMap (live .l12979c))
      1 0x12979c bytes_l12979c b_l12979c := by
  have f0 : InstrSpec 0x12979c [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x12979c) (fun _ => nopEffect 0x12979c 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12979c 4).toInstrSpec (nop_m_effect_step 0x12979c [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1297a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l12979c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12979c :=
  Rest.liftedBlock (rest_l12979c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12979c x hx)

theorem rest_l129c30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c30 bytes_l129c30) (entryMap (live .l129c30))
      12 0x129c30 bytes_l129c30 b_l129c30 := by
  have f0 : InstrSpec 0x129c30 [0x55] (PushPre 0x129c30 1) (pushR64Effect 0x129c30 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c30 1 5).toInstrSpec (push_r64_effect_step 0x129c30 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129c31 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129c31) (movR64R64Effect 0x129c31 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129c31 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129c31 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129c34 [0x41, 0x57] (PushPre 0x129c34 2) (pushR64Effect 0x129c34 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c34 2 15).toInstrSpec (push_r64_rex_effect_step 0x129c34 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129c36 [0x41, 0x56] (PushPre 0x129c36 2) (pushR64Effect 0x129c36 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c36 2 14).toInstrSpec (push_r64_rex_effect_step 0x129c36 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x129c38 [0x41, 0x54] (PushPre 0x129c38 2) (pushR64Effect 0x129c38 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c38 2 12).toInstrSpec (push_r64_rex_effect_step 0x129c38 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129c3a [0x53] (PushPre 0x129c3a 1) (pushR64Effect 0x129c3a 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c3a 1 3).toInstrSpec (push_r64_effect_step 0x129c3a 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x129c3b [0x4C, 0x89, 0xC3] (fun s => s.RIP = 0x129c3b) (movR64R64Effect 0x129c3b 3 8)
      [.gpr 8] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x129c3b 3 8).toInstrSpec (mov_r64_r64_effect_step 0x129c3b 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129c3e [0x49, 0x89, 0xCE] (fun s => s.RIP = 0x129c3e) (movR64R64Effect 0x129c3e 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x129c3e 14 1).toInstrSpec (mov_r64_r64_effect_step 0x129c3e 0x49 0xce (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129c41 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x129c41) (movR64R64Effect 0x129c41 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x129c41 12 6).toInstrSpec (mov_r64_r64_effect_step 0x129c41 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129c44 [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x129c44) (movR64R64Effect 0x129c44 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x129c44 15 7).toInstrSpec (mov_r64_r64_effect_step 0x129c44 0x49 0xff (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129c47 [0x83, 0xFA, 0xFF] (fun s => s.RIP = 0x129c47) (cmpR32Imm8Effect 0x129c47 3 2 0xff)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x129c47 3 2 0xff).toInstrSpec (cmp_r32_imm8_effect_step 0x129c47 0xfa 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c34) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c36) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c38) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c3a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c3b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c3e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c41) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 68), (13, 13), (14, 66), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c44) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c47) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c4a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 74) (jcc_rel8_effect_step 0x129c4a 4 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129c30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c30 :=
  Rest.liftedBlock (rest_l129c30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c30 x hx)

theorem rest_l129c4c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c4c bytes_l129c4c) (entryMap (live .l129c4c))
      2 0x129c4c bytes_l129c4c b_l129c4c := by
  have f0 : InstrSpec 0x129c4c [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x129c4c) (movR64R64Effect 0x129c4c 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129c4c 7 15).toInstrSpec (mov_r64_r64_effect_step 0x129c4c 0x4c 0xff (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129c4f [0x89, 0xD6] (fun s => s.RIP = 0x129c4f) (movR32R32Effect 0x129c4f 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x129c4f 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x129c4f 0xd6 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (15, 15)]) (p' := 0x129c4f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (15, 15)]) (p' := 0x129c51) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l129c4c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c4c :=
  Rest.liftedBlock (rest_l129c4c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c4c x hx)

theorem rest_l129c56 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c56 bytes_l129c56) (entryMap (live .l129c56))
      4 0x129c56 bytes_l129c56 b_l129c56 := by
  have f0 : InstrSpec 0x129c56 [0x89, 0xC1] (fun s => s.RIP = 0x129c56) (movR32R32Effect 0x129c56 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x129c56 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x129c56 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x129c58 [0xB0, 0x01] (fun s => s.RIP = 0x129c58) (movR8Imm8Effect 0x129c58 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x129c58 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x129c58 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x129c5a [0x84, 0xC9] (fun s => s.RIP = 0x129c5a) (testR8R8Effect 0x129c5a 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129c5a 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x129c5a 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c58) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c5a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c5c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x129c5c 5 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129c56 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c56 :=
  Rest.liftedBlock (rest_l129c56 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c56 x hx)

theorem rest_l129c5e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c5e bytes_l129c5e) (entryMap (live .l129c5e))
      2 0x129c5e bytes_l129c5e b_l129c5e := by
  have f0 : InstrSpec 0x129c5e [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x129c5e) (testR64R64Effect 0x129c5e 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x129c5e 14 14).toInstrSpec (test_r64_r64_effect_step 0x129c5e 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c61) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x129c61 4 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129c5e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c5e :=
  Rest.liftedBlock (rest_l129c5e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c5e x hx)

theorem rest_l129c63 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c63 bytes_l129c63) (entryMap (live .l129c63))
      9 0x129c63 bytes_l129c63 b_l129c63 := by
  have f0 : InstrSpec 0x129c63 [0x49, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x129c63 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x129c63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x129c63 0 (.sib 12 none 0 (.d8 0x18)))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x129c63 0 (.sib 12 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x129c63 0x49 (by decide) 0 (.sib 12 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x129c68 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x129c68) (movR64R64Effect 0x129c68 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129c68 7 15).toInstrSpec (mov_r64_r64_effect_step 0x129c68 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129c6b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x129c6b) (movR64R64Effect 0x129c6b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x129c6b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x129c6b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129c6e [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x129c6e) (movR64R64Effect 0x129c6e 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x129c6e 2 3).toInstrSpec (mov_r64_r64_effect_step 0x129c6e 0x48 0xda (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129c71 [0x5B] (PopPre 0x129c71) (popR64Effect 0x129c71 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c71 1 3).toInstrSpec (pop_r64_effect_step 0x129c71 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129c72 [0x41, 0x5C] (PopPre 0x129c72) (popR64Effect 0x129c72 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c72 2 12).toInstrSpec (pop_r64_rex_effect_step 0x129c72 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x129c74 [0x41, 0x5E] (PopPre 0x129c74) (popR64Effect 0x129c74 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c74 2 14).toInstrSpec (pop_r64_rex_effect_step 0x129c74 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x129c76 [0x41, 0x5F] (PopPre 0x129c76) (popR64Effect 0x129c76 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c76 2 15).toInstrSpec (pop_r64_rex_effect_step 0x129c76 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x129c78 [0x5D] (PopPre 0x129c78) (popR64Effect 0x129c78 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c78 1 5).toInstrSpec (pop_r64_effect_step 0x129c78 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c68) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c6b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c6e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c71) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 57), (12, 12), (14, 14), (15, 15)]) (p' := 0x129c72) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 59), (14, 14), (15, 15)]) (p' := 0x129c74) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 61), (15, 15)]) (p' := 0x129c76) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(4, 63)]) (p' := 0x129c78) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := []) (p' := 0x129c79) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l129c63 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c63 :=
  Rest.liftedBlock (rest_l129c63 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c63 x hx)

theorem rest_l129c7b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c7b bytes_l129c7b) (entryMap (live .l129c7b))
      1 0x129c7b bytes_l129c7b b_l129c7b := by
  have f0 : InstrSpec 0x129c7b [0x31, 0xC0] (fun s => s.RIP = 0x129c7b) (xorR32R32Effect 0x129c7b 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129c7b 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x129c7b 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c7d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l129c7b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c7b :=
  Rest.liftedBlock (rest_l129c7b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c7b x hx)

theorem rest_l129c7d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c7d bytes_l129c7d) (entryMap (live .l129c7d))
      6 0x129c7d bytes_l129c7d b_l129c7d := by
  have f0 : InstrSpec 0x129c7d [0x5B] (PopPre 0x129c7d) (popR64Effect 0x129c7d 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c7d 1 3).toInstrSpec (pop_r64_effect_step 0x129c7d 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129c7e [0x41, 0x5C] (PopPre 0x129c7e) (popR64Effect 0x129c7e 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c7e 2 12).toInstrSpec (pop_r64_rex_effect_step 0x129c7e 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129c80 [0x41, 0x5E] (PopPre 0x129c80) (popR64Effect 0x129c80 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c80 2 14).toInstrSpec (pop_r64_rex_effect_step 0x129c80 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x129c82 [0x41, 0x5F] (PopPre 0x129c82) (popR64Effect 0x129c82 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c82 2 15).toInstrSpec (pop_r64_rex_effect_step 0x129c82 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x129c84 [0x5D] (PopPre 0x129c84) (popR64Effect 0x129c84 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129c84 1 5).toInstrSpec (pop_r64_effect_step 0x129c84 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x129c85 [0xC3] (RetPre 0x129c85) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x129c85).toInstrSpec (ret_effect_step 0x129c85) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 54), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 57), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c80) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 60), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c82) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c84) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 66), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129c85) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l129c7d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c7d :=
  Rest.liftedBlock (rest_l129c7d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c7d x hx)

theorem rest_l129c90 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129c90 bytes_l129c90) (entryMap (live .l129c90))
      15 0x129c90 bytes_l129c90 b_l129c90 := by
  have f0 : InstrSpec 0x129c90 [0x55] (PushPre 0x129c90 1) (pushR64Effect 0x129c90 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129c90 1 5).toInstrSpec (push_r64_effect_step 0x129c90 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129c91 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129c91) (movR64R64Effect 0x129c91 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129c91 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129c91 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129c94 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x129c94) (subR64Imm8Effect 0x129c94 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129c94 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x129c94 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129c98 [0x48, 0x89, 0x75, 0xF8] (StorePre 0x129c98 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x129c98 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129c98 6 (.base 5 (.d8 0xf8)))
      [.gpr 6, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129c98 6 (.base 5 (.d8 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x129c98 0x48 (by decide) 6 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x129c9c [0x48, 0x89, 0x7D, 0xF0] (StorePre 0x129c9c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129c9c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129c9c 7 (.base 5 (.d8 0xf0)))
      [.gpr 7, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129c9c 7 (.base 5 (.d8 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x129c9c 0x48 (by decide) 7 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x129ca0 [0x48, 0x8D, 0x45, 0xF8] (fun s => s.RIP = 0x129ca0) (leaR64Effect 0x129ca0 0 (.base 5 (.d8 0xf8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129ca0 0 (.base 5 (.d8 0xf8))).toInstrSpec (lea_r64_effect_step 0x129ca0 0x48 (by decide) 0 (.base 5 (.d8 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129ca4 [0x48, 0x89, 0x45, 0xD0] (StorePre 0x129ca4 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129ca4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129ca4 0 (.base 5 (.d8 0xd0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129ca4 0 (.base 5 (.d8 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x129ca4 0x48 (by decide) 0 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x129ca8 [0x48, 0x8D, 0x05, 0x81, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x129ca8) (leaR64Effect 0x129ca8 0 (.rip 0x781))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x129ca8 0 (.rip 0x781)).toInstrSpec (lea_r64_effect_step 0x129ca8 0x48 (by decide) 0 (.rip 0x781) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x129caf [0x48, 0x89, 0x45, 0xD8] (StorePre 0x129caf 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129caf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129caf 0 (.base 5 (.d8 0xd8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129caf 0 (.base 5 (.d8 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x129caf 0x48 (by decide) 0 (.base 5 (.d8 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x129cb3 [0x48, 0x8D, 0x4D, 0xF0] (fun s => s.RIP = 0x129cb3) (leaR64Effect 0x129cb3 1 (.base 5 (.d8 0xf0)))
      [.gpr 5] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x129cb3 1 (.base 5 (.d8 0xf0))).toInstrSpec (lea_r64_effect_step 0x129cb3 0x48 (by decide) 1 (.base 5 (.d8 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x129cb7 [0x48, 0x89, 0x4D, 0xE0] (StorePre 0x129cb7 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129cb7 1 (.base 5 (.d8 0xe0)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129cb7 1 (.base 5 (.d8 0xe0))).toInstrSpec (mov_m64_r64_effect_step 0x129cb7 0x48 (by decide) 1 (.base 5 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x129cbb [0x48, 0x89, 0x45, 0xE8] (StorePre 0x129cbb 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129cbb 0 (.base 5 (.d8 0xe8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x129cbb 0 (.base 5 (.d8 0xe8))).toInstrSpec (mov_m64_r64_effect_step 0x129cbb 0x48 (by decide) 0 (.base 5 (.d8 0xe8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x129cbf [0x48, 0x8D, 0x3D, 0x9C, 0x80, 0x0D, 0x00] (fun s => s.RIP = 0x129cbf) (leaR64Effect 0x129cbf 7 (.rip 0xd809c))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129cbf 7 (.rip 0xd809c)).toInstrSpec (lea_r64_effect_step 0x129cbf 0x48 (by decide) 7 (.rip 0xd809c) (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x129cc6 [0x48, 0x8D, 0x75, 0xD0] (fun s => s.RIP = 0x129cc6) (leaR64Effect 0x129cc6 6 (.base 5 (.d8 0xd0)))
      [.gpr 5] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x129cc6 6 (.base 5 (.d8 0xd0))).toInstrSpec (lea_r64_effect_step 0x129cc6 0x48 (by decide) 6 (.base 5 (.d8 0xd0)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x129cca [0xFF, 0x15, 0x10, 0xA1, 0x0D, 0x00] (GoesTo (CallMemPre 0x129cca (.rip 0xda110)) (callEffect (callMemPtr 0x129cca (.rip 0xda110)) (0x129cca + BitVec.ofNat 64 (callMemLen (.rip 0xda110)))) 0x129770) (callEffect (callMemPtr 0x129cca (.rip 0xda110)) (0x129cca + BitVec.ofNat 64 (callMemLen (.rip 0xda110))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129cca (.rip 0xda110)).toInstrSpec (call_m64_effect_step 0x129cca (.rip 0xda110) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x129770
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 53), (5, 5), (6, 6), (7, 7)]) (p' := 0x129c91) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (4, 53), (5, 55), (6, 6), (7, 7)]) (p' := 0x129c94) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129c98) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129c9c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129ca0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129ca4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129ca8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129caf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129cb3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129cb7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129cbb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 6), (7, 7)]) (p' := 0x129cbf) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 6), (7, 71)]) (p' := 0x129cc6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 57), (5, 55), (6, 73), (7, 71)]) (p' := 0x129cca) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 64), (1, 67), (2, 2), (4, 75), (5, 55), (6, 73), (7, 71)]) (p' := 0x129770) f14 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l129c90 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129c90 :=
  Rest.liftedBlock (rest_l129c90 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129c90 x hx)

theorem rest_l129cd0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129cd0 bytes_l129cd0) (entryMap (live .l129cd0))
      8 0x129cd0 bytes_l129cd0 b_l129cd0 := by
  have f0 : InstrSpec 0x129cd0 [0x55] (PushPre 0x129cd0 1) (pushR64Effect 0x129cd0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x129cd0 1 5).toInstrSpec (push_r64_effect_step 0x129cd0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x129cd1 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x129cd1) (movR64R64Effect 0x129cd1 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x129cd1 5 4).toInstrSpec (mov_r64_r64_effect_step 0x129cd1 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129cd4 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x129cd4) (subR64Imm8Effect 0x129cd4 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x129cd4 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x129cd4 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129cd8 [0x0F, 0xB6, 0x0F] (LoadPre 0x129cd8 (fun s => AddrMode.addr (.base 7 .none) s (0x129cd8 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x129cd8 3 1 (.base 7 .none))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x129cd8 3 1 (.base 7 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x129cd8 1 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x129cdb [0xB8, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129cdb) (movR32Imm32Effect 0x129cdb 5 0 0x3)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x129cdb 5 0 0x3).toInstrSpec (mov_r32_imm32_effect_step 0x129cdb 0xb8 (by decide) 0x3) pre_rip
  have f5 : InstrSpec 0x129ce0 [0x89, 0xCA] (fun s => s.RIP = 0x129ce0) (movR32R32Effect 0x129ce0 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x129ce0 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x129ce0 0xca (by decide)) pre_rip
  have f6 : InstrSpec 0x129ce2 [0x80, 0xF9, 0x0A] (fun s => s.RIP = 0x129ce2) (cmpR8Imm8Effect 0x129ce2 3 1 0xa)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x129ce2 3 1 0xa).toInstrSpec (cmp_r8_imm8_effect_step 0x129ce2 0xf9 0xa (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cd1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cd4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cd8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cdb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 59), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ce0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 59), (2, 63), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ce2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 59), (2, 63), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ce5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 67) (jcc_rel8_effect_step 0x129ce5 2 0x2c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129cd0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129cd0 :=
  Rest.liftedBlock (rest_l129cd0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129cd0 x hx)

theorem rest_l129ce7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129ce7 bytes_l129ce7) (entryMap (live .l129ce7))
      12 0x129ce7 bytes_l129ce7 b_l129ce7 := by
  have f0 : InstrSpec 0x129ce7 [0x0F, 0xB6, 0xC1] (fun s => s.RIP = 0x129ce7) (movzxR32R8Effect 0x129ce7 3 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x129ce7 3 0 1).toInstrSpec (movzx_r32_r8_effect_step 0x129ce7 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129cea [0x8D, 0x14, 0x80] (fun s => s.RIP = 0x129cea) (leaR32Effect 0x129cea 3 2 (.sib 0 (some 0) 2 .none))
      [.gpr 0, .gpr 0] [] [.reg 2, .rip] :=
    (leaR32Effect_footprint 0x129cea 3 2 (.sib 0 (some 0) 2 .none)).toInstrSpec (lea_r32_effect_step 0x129cea 2 (.sib 0 (some 0) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129ced [0x8D, 0x14, 0xD0] (fun s => s.RIP = 0x129ced) (leaR32Effect 0x129ced 3 2 (.sib 0 (some 2) 3 .none))
      [.gpr 0, .gpr 2] [] [.reg 2, .rip] :=
    (leaR32Effect_footprint 0x129ced 3 2 (.sib 0 (some 2) 3 .none)).toInstrSpec (lea_r32_effect_step 0x129ced 2 (.sib 0 (some 2) 3 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129cf0 [0xC1, 0xEA, 0x0C] (fun s => s.RIP = 0x129cf0) (shrR32Effect 0x129cf0 3 2 12)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x129cf0 3 2 12).toInstrSpec (shr_r32_imm8_effect_step 0x129cf0 0xea 0xc (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129cf3 [0x6B, 0xC2, 0x64] (fun s => s.RIP = 0x129cf3) (imulR32R32Imm8Effect 0x129cf3 3 0 2 0x64)
      [.gpr 2] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x129cf3 3 0 2 0x64).toInstrSpec (imul_r32_r32_imm8_effect_step 0x129cf3 0xc2 (by decide) 0x64) pre_rip
  have f5 : InstrSpec 0x129cf6 [0x89, 0xCF] (fun s => s.RIP = 0x129cf6) (movR32R32Effect 0x129cf6 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x129cf6 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x129cf6 0xcf (by decide)) pre_rip
  have f6 : InstrSpec 0x129cf8 [0x40, 0x28, 0xC7] (fun s => s.RIP = 0x129cf8) (subR8R8Effect 0x129cf8 3 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (subR8R8Effect_footprint 0x129cf8 3 7 0).toInstrSpec (sub_r8_r8_rex_effect_step 0x129cf8 0x40 0xc7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x129cfb [0x40, 0x0F, 0xB6, 0xC7] (fun s => s.RIP = 0x129cfb) (movzxR32R8Effect 0x129cfb 4 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x129cfb 4 0 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x129cfb 0x40 (by decide) 0xc7 (by decide)) pre_rip
  have f8 : InstrSpec 0x129cff [0x48, 0x8D, 0x3D, 0x3D, 0x9F, 0x0D, 0x00] (fun s => s.RIP = 0x129cff) (leaR64Effect 0x129cff 7 (.rip 0xd9f3d))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x129cff 7 (.rip 0xd9f3d)).toInstrSpec (lea_r64_effect_step 0x129cff 0x48 (by decide) 7 (.rip 0xd9f3d) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x129d06 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x129d06 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x129d06 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x129d06 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x129d06 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x129d06 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x129d0a [0x66, 0x89, 0x45, 0xFE] (StorePre 0x129d0a 4 (fun s => AddrMode.addr (.base 5 (.d8 0xfe)) s (0x129d0a + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x129d0a 4 0 (.base 5 (.d8 0xfe)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM16R16Effect_footprint 0x129d0a 4 0 (.base 5 (.d8 0xfe))).toInstrSpec (mov_m16_r16_effect_step 0x129d0a 0 (.base 5 (.d8 0xfe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x129d0e [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129d0e) (movR32Imm32Effect 0x129d0e 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x129d0e 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x129d0e 0xb8 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129ced) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cf0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cf3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cf6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cf8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cfb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129cff) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d06) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d0a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d0e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d13) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l129ce7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129ce7 :=
  Rest.liftedBlock (rest_l129ce7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129ce7 x hx)

theorem rest_l129d13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129d13 bytes_l129d13) (entryMap (live .l129d13))
      6 0x129d13 bytes_l129d13 b_l129d13 := by
  have f0 : InstrSpec 0x129d13 [0x84, 0xD2] (fun s => s.RIP = 0x129d13) (testR8R8Effect 0x129d13 2 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129d13 2 2 2).toInstrSpec (test_r8_r8_effect_step 0x129d13 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129d15 [0x40, 0x0F, 0x94, 0xC7] (fun s => s.RIP = 0x129d15) (atFlags (condHolds 4) (setccR8Effect 0x129d15 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x129d15 4 7 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x129d15 4 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f2 : InstrSpec 0x129d19 [0x84, 0xC9] (fun s => s.RIP = 0x129d19) (testR8R8Effect 0x129d19 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129d19 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x129d19 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129d1b [0x0F, 0x95, 0xC1] (fun s => s.RIP = 0x129d1b) (atFlags (condHolds 5) (setccR8Effect 0x129d1b 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x129d1b 3 1 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x129d1b 5 0xc1 (by decide) (by decide) c)) pre_rip
  have f4 : InstrSpec 0x129d1e [0x40, 0x84, 0xF9] (fun s => s.RIP = 0x129d1e) (testR8R8Effect 0x129d1e 3 1 7)
      [.gpr 1, .gpr 7] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x129d1e 3 1 7).toInstrSpec (test_r8_r8_rex_effect_step 0x129d1e 0x40 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d15) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d19) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d1b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d1e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d21) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x129d21 5 0x16) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l129d13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129d13 :=
  Rest.liftedBlock (rest_l129d13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129d13 x hx)

theorem rest_l129d23 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129d23 bytes_l129d23) (entryMap (live .l129d23))
      5 0x129d23 bytes_l129d23 b_l129d23 := by
  have f0 : InstrSpec 0x129d23 [0x0F, 0xB6, 0xCA] (fun s => s.RIP = 0x129d23) (movzxR32R8Effect 0x129d23 3 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x129d23 3 1 2).toInstrSpec (movzx_r32_r8_effect_step 0x129d23 0xca (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129d26 [0x48, 0x8D, 0x15, 0x16, 0x9F, 0x0D, 0x00] (fun s => s.RIP = 0x129d26) (leaR64Effect 0x129d26 2 (.rip 0xd9f16))
      [] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x129d26 2 (.rip 0xd9f16)).toInstrSpec (lea_r64_effect_step 0x129d26 0x48 (by decide) 2 (.rip 0xd9f16) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129d2d [0x0F, 0xB6, 0x4C, 0x4A, 0x01] (LoadPre 0x129d2d (fun s => AddrMode.addr (.sib 2 (some 1) 1 (.d8 0x1)) s (0x129d2d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x129d2d 5 1 (.sib 2 (some 1) 1 (.d8 0x1)))
      [.gpr 2, .gpr 1] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x129d2d 5 1 (.sib 2 (some 1) 1 (.d8 0x1))).toInstrSpec (movzx_r32_m8_effect_step 0x129d2d 1 (.sib 2 (some 1) 1 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x129d32 [0x88, 0x4C, 0x05, 0xFC] (StorePre 0x129d32 4 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xfc)) s (0x129d32 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x129d32 4 1 (.sib 5 (some 0) 0 (.d8 0xfc)))
      [.gpr 1, .gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x129d32 4 1 (.sib 5 (some 0) 0 (.d8 0xfc))).toInstrSpec (mov_m8_r8_effect_step 0x129d32 1 (by decide) (.sib 5 (some 0) 0 (.d8 0xfc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x129d36 [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x129d36) (decR64Effect 0x129d36 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x129d36 0).toInstrSpec (dec_r64_effect_step 0x129d36 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d26) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d2d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d32) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d36) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d39) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l129d23 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129d23 :=
  Rest.liftedBlock (rest_l129d23 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129d23 x hx)

theorem rest_l129d39 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129d39 bytes_l129d39) (entryMap (live .l129d39))
      9 0x129d39 bytes_l129d39 b_l129d39 := by
  have f0 : InstrSpec 0x129d39 [0x41, 0xB9, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129d39) (movR32Imm32Effect 0x129d39 6 9 0x3)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x129d39 6 9 0x3).toInstrSpec (mov_r32_imm32_rex_effect_step 0x129d39 0x41 0xb9 (by decide) (by decide) 0x3) pre_rip
  have f1 : InstrSpec 0x129d3f [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x129d3f) (subR64R64Effect 0x129d3f 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x129d3f 9 0).toInstrSpec (sub_r64_r64_effect_step 0x129d3f 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x129d42 [0x4C, 0x8D, 0x04, 0x28] (fun s => s.RIP = 0x129d42) (leaR64Effect 0x129d42 8 (.sib 0 (some 5) 0 .none))
      [.gpr 0, .gpr 5] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x129d42 8 (.sib 0 (some 5) 0 .none)).toInstrSpec (lea_r64_effect_step 0x129d42 0x4c (by decide) 0 (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x129d46 [0x49, 0x83, 0xC0, 0xFD] (fun s => s.RIP = 0x129d46) (addR64Imm8Effect 0x129d46 8 0xfd)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129d46 8 0xfd).toInstrSpec (add_r64_imm8_effect_step 0x129d46 0x49 0xc0 0xfd (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x129d4a [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129d4a) (movR32Imm32Effect 0x129d4a 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x129d4a 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x129d4a 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x129d4f [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x129d4f) (movR64R64Effect 0x129d4f 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x129d4f 7 6).toInstrSpec (mov_r64_r64_effect_step 0x129d4f 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x129d52 [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x129d52) (movR32Imm32Effect 0x129d52 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x129d52 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x129d52 0xbe (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x129d57 [0x31, 0xC9] (fun s => s.RIP = 0x129d57) (xorR32R32Effect 0x129d57 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x129d57 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x129d57 0xc9 (by decide)) pre_rip
  have f8 : InstrSpec 0x129d59 [0xFF, 0x15, 0x89, 0xA0, 0x0D, 0x00] (GoesTo (CallMemPre 0x129d59 (.rip 0xda089)) (callEffect (callMemPtr 0x129d59 (.rip 0xda089)) (0x129d59 + BitVec.ofNat 64 (callMemLen (.rip 0xda089)))) 0x128b20) (callEffect (callMemPtr 0x129d59 (.rip 0xda089)) (0x129d59 + BitVec.ofNat 64 (callMemLen (.rip 0xda089))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x129d59 (.rip 0xda089)).toInstrSpec (call_m64_effect_step 0x129d59 (.rip 0xda089) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x128b20
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d3f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d42) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 57), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d46) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d4a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d4f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d52) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d57) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d59) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 69), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b20) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l129d39 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129d39 :=
  Rest.liftedBlock (rest_l129d39 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129d39 x hx)

theorem rest_l129d5f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x129d5f bytes_l129d5f) (entryMap (live .l129d5f))
      3 0x129d5f bytes_l129d5f b_l129d5f := by
  have f0 : InstrSpec 0x129d5f [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x129d5f) (addR64Imm8Effect 0x129d5f 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x129d5f 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x129d5f 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x129d63 [0x5D] (PopPre 0x129d63) (popR64Effect 0x129d63 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x129d63 1 5).toInstrSpec (pop_r64_effect_step 0x129d63 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x129d64 [0xC3] (RetPre 0x129d64) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x129d64).toInstrSpec (ret_effect_step 0x129d64) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d63) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129d64) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l129d5f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l129d5f :=
  Rest.liftedBlock (rest_l129d5f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l129d5f x hx)

theorem rest_l12a050 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a050 bytes_l12a050) (entryMap (live .l12a050))
      4 0x12a050 bytes_l12a050 b_l12a050 := by
  have f0 : InstrSpec 0x12a050 [0x48, 0x8B, 0x07] (LoadPre 0x12a050 (fun s => AddrMode.addr (.base 7 .none) s (0x12a050 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a050 0 (.base 7 .none))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12a050 0 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a050 0x48 (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a053 [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x12a053 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a053 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a053 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12a053 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a053 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a057 [0x48, 0x8B, 0x49, 0x18] (LoadPre 0x12a057 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x12a057 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a057 1 (.base 1 (.d8 0x18)))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12a057 1 (.base 1 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12a057 0x48 (by decide) 1 (.base 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a05b [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12a05b) (movR64R64Effect 0x12a05b 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a05b 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12a05b 0x48 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (7, 7)]) (p' := 0x12a053) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (7, 7)]) (p' := 0x12a057) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (7, 7)]) (p' := 0x12a05b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53)]) (p' := 0x12a05e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l12a050 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a050 :=
  Rest.liftedBlock (rest_l12a050 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a050 x hx)

theorem rest_l12a070 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a070 bytes_l12a070) (entryMap (live .l12a070))
      5 0x12a070 bytes_l12a070 b_l12a070 := by
  have f0 : InstrSpec 0x12a070 [0x48, 0x89, 0xF0] (fun s => s.RIP = 0x12a070) (movR64R64Effect 0x12a070 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a070 0 6).toInstrSpec (mov_r64_r64_effect_step 0x12a070 0x48 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a073 [0x48, 0x8B, 0x37] (LoadPre 0x12a073 (fun s => AddrMode.addr (.base 7 .none) s (0x12a073 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a073 6 (.base 7 .none))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12a073 6 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a073 0x48 (by decide) 6 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a076 [0x48, 0x8B, 0x57, 0x08] (LoadPre 0x12a076 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a076 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a076 2 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12a076 2 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a076 0x48 (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a07a [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12a07a) (movR64R64Effect 0x12a07a 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a07a 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12a07a 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a07d [0xFF, 0x25, 0x85, 0x9D, 0x0D, 0x00] (GoesTo (JmpMemPre 0x12a07d 6 (.rip 0xd9d85)) (jmpM64Effect 0x12a07d 6 (.rip 0xd9d85)) 0x129100) (jmpM64Effect 0x12a07d 6 (.rip 0xd9d85))
      [] [] [.rip] :=
    ((jmpM64Effect_footprint 0x12a07d 6 (.rip 0xd9d85)).toInstrSpec (jmp_m64_effect_step 0x12a07d (.rip 0xd9d85) (by decide) (by decide) (by decide)) (JmpMemPre.of_addr rfl)).goesTo 0x129100
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a073) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a076) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a07a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a07d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x129100) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 62) (by decide) rfl

theorem block_l12a070 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a070 :=
  Rest.liftedBlock (rest_l12a070 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a070 x hx)

theorem rest_l12a100 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a100 bytes_l12a100) (entryMap (live .l12a100))
      6 0x12a100 bytes_l12a100 b_l12a100 := by
  have f0 : InstrSpec 0x12a100 [0x48, 0x8B, 0x06] (LoadPre 0x12a100 (fun s => AddrMode.addr (.base 6 .none) s (0x12a100 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a100 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12a100 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a100 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a103 [0x48, 0x8B, 0x76, 0x08] (LoadPre 0x12a103 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12a103 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a103 6 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12a103 6 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a103 0x48 (by decide) 6 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a107 [0x48, 0x8B, 0x17] (LoadPre 0x12a107 (fun s => AddrMode.addr (.base 7 .none) s (0x12a107 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a107 2 (.base 7 .none))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12a107 2 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a107 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x12a10a [0x48, 0x8B, 0x4F, 0x08] (LoadPre 0x12a10a (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a10a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a10a 1 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12a10a 1 (.base 7 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12a10a 0x48 (by decide) 1 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x12a10e [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x12a10e) (movR64R64Effect 0x12a10e 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a10e 7 0).toInstrSpec (mov_r64_r64_effect_step 0x12a10e 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a111 [0xFF, 0x25, 0x11, 0x9D, 0x0D, 0x00] (GoesTo (JmpMemPre 0x12a111 6 (.rip 0xd9d11)) (jmpM64Effect 0x12a111 6 (.rip 0xd9d11)) 0x1293a0) (jmpM64Effect 0x12a111 6 (.rip 0xd9d11))
      [] [] [.rip] :=
    ((jmpM64Effect_footprint 0x12a111 6 (.rip 0xd9d11)).toInstrSpec (jmp_m64_effect_step 0x12a111 (.rip 0xd9d11) (by decide) (by decide) (by decide)) (JmpMemPre.of_addr rfl)).goesTo 0x1293a0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a103) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a107) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a10a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a10e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a111) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1293a0) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 64) (by decide) rfl

theorem block_l12a100 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a100 :=
  Rest.liftedBlock (rest_l12a100 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a100 x hx)

theorem rest_l12a430 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a430 bytes_l12a430) (entryMap (live .l12a430))
      10 0x12a430 bytes_l12a430 b_l12a430 := by
  have f0 : InstrSpec 0x12a430 [0x55] (PushPre 0x12a430 1) (pushR64Effect 0x12a430 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a430 1 5).toInstrSpec (push_r64_effect_step 0x12a430 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x12a431 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x12a431) (movR64R64Effect 0x12a431 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x12a431 5 4).toInstrSpec (mov_r64_r64_effect_step 0x12a431 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a434 [0x53] (PushPre 0x12a434 1) (pushR64Effect 0x12a434 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12a434 1 3).toInstrSpec (push_r64_effect_step 0x12a434 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12a435 [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x12a435) (subR64Imm8Effect 0x12a435 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x12a435 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x12a435 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a439 [0x4C, 0x8B, 0x07] (LoadPre 0x12a439 (fun s => AddrMode.addr (.base 7 .none) s (0x12a439 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a439 8 (.base 7 .none))
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x12a439 8 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a439 0x4c (by decide) 0 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12a43c [0xB8, 0x14, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a43c) (movR32Imm32Effect 0x12a43c 5 0 0x14)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x12a43c 5 0 0x14).toInstrSpec (mov_r32_imm32_effect_step 0x12a43c 0xb8 (by decide) 0x14) pre_rip
  have f6 : InstrSpec 0x12a441 [0x48, 0x8D, 0x3D, 0xFB, 0x97, 0x0D, 0x00] (fun s => s.RIP = 0x12a441) (leaR64Effect 0x12a441 7 (.rip 0xd97fb))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12a441 7 (.rip 0xd97fb)).toInstrSpec (lea_r64_effect_step 0x12a441 0x48 (by decide) 7 (.rip 0xd97fb) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a448 [0x4C, 0x89, 0xC2] (fun s => s.RIP = 0x12a448) (movR64R64Effect 0x12a448 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a448 2 8).toInstrSpec (mov_r64_r64_effect_step 0x12a448 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12a44b [0x49, 0x81, 0xF8, 0xE8, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x12a44b) (cmpR64Imm32Effect 0x12a44b 8 0x3e8)
      [.gpr 8] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x12a44b 8 0x3e8).toInstrSpec (cmp_r64_imm32_effect_step 0x12a44b 0x49 0xf8 0x3e8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a431) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a434) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a435) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a439) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a43c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a441) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 1), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a448) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a44b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a452) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x12a452 2 0x6d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a430 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a430 :=
  Rest.liftedBlock (rest_l12a430 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a430 x hx)

theorem rest_l12a454 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a454 bytes_l12a454) (entryMap (live .l12a454))
      3 0x12a454 bytes_l12a454 b_l12a454 := by
  have f0 : InstrSpec 0x12a454 [0x49, 0xB9, 0x4B, 0x59, 0x86, 0x38, 0xD6, 0xC5, 0x6D, 0x34] (fun s => s.RIP = 0x12a454) (movR64Imm64Effect 0x12a454 9 0x346dc5d63886594b)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x12a454 9 0x346dc5d63886594b).toInstrSpec (mov_r64_imm64_effect_step 0x12a454 0x49 0xb9 (by decide) (by decide) 0x346dc5d63886594b) pre_rip
  have f1 : InstrSpec 0x12a45e [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x12a45e) (movR64R64Effect 0x12a45e 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a45e 1 8).toInstrSpec (mov_r64_r64_effect_step 0x12a45e 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a461 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a461) (fun _ => nopEffect 0x12a461 15)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12a461 15).toInstrSpec (nop_m_effect_step 0x12a461 [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a45e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a461) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a470) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l12a454 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a454 :=
  Rest.liftedBlock (rest_l12a454 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a454 x hx)

theorem rest_l12a470 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a470 bytes_l12a470) (entryMap (live .l12a470))
      20 0x12a470 bytes_l12a470 b_l12a470 := by
  have f0 : InstrSpec 0x12a470 [0x49, 0x89, 0xC2] (fun s => s.RIP = 0x12a470) (movR64R64Effect 0x12a470 10 0)
      [.gpr 0] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x12a470 10 0).toInstrSpec (mov_r64_r64_effect_step 0x12a470 0x49 0xc2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a473 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x12a473) (movR64R64Effect 0x12a473 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a473 0 1).toInstrSpec (mov_r64_r64_effect_step 0x12a473 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a476 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x12a476) (mulR64Effect 0x12a476 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x12a476 9).toInstrSpec (mul_r64_effect_step 0x12a476 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a479 [0x48, 0xC1, 0xEA, 0x0B] (fun s => s.RIP = 0x12a479) (shrR64Effect 0x12a479 4 2 11)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a479 4 2 11).toInstrSpec (shr_r64_imm8_effect_step 0x12a479 0x48 0xea 0xb (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a47d [0x69, 0xC2, 0x10, 0x27, 0x00, 0x00] (fun s => s.RIP = 0x12a47d) (imulR32R32Imm32Effect 0x12a47d 6 0 2 0x2710)
      [.gpr 2] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x12a47d 6 0 2 0x2710).toInstrSpec (imul_r32_r32_imm32_effect_step 0x12a47d 0xc2 (by decide) 0x2710) pre_rip
  have f5 : InstrSpec 0x12a483 [0x41, 0x89, 0xCB] (fun s => s.RIP = 0x12a483) (movR32R32Effect 0x12a483 3 11 1)
      [.gpr 1] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x12a483 3 11 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x12a483 0x41 0xcb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12a486 [0x41, 0x29, 0xC3] (fun s => s.RIP = 0x12a486) (subR32R32Effect 0x12a486 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a486 3 11 0).toInstrSpec (sub_r32_r32_rex_effect_step 0x12a486 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a489 [0x41, 0x69, 0xC3, 0x7B, 0x14, 0x00, 0x00] (fun s => s.RIP = 0x12a489) (imulR32R32Imm32Effect 0x12a489 7 0 11 0x147b)
      [.gpr 11] [] [.reg 0, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x12a489 7 0 11 0x147b).toInstrSpec (imul_r32_r32_imm32_rex_effect_step 0x12a489 0x41 (by decide) 0xc3 (by decide) 0x147b) pre_rip
  have f8 : InstrSpec 0x12a490 [0xC1, 0xE8, 0x13] (fun s => s.RIP = 0x12a490) (shrR32Effect 0x12a490 3 0 19)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a490 3 0 19).toInstrSpec (shr_r32_imm8_effect_step 0x12a490 0xe8 0x13 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12a493 [0x6B, 0xD8, 0x64] (fun s => s.RIP = 0x12a493) (imulR32R32Imm8Effect 0x12a493 3 3 0 0x64)
      [.gpr 0] [] [.reg 3, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x12a493 3 3 0 0x64).toInstrSpec (imul_r32_r32_imm8_effect_step 0x12a493 0xd8 (by decide) 0x64) pre_rip
  have f10 : InstrSpec 0x12a496 [0x41, 0x29, 0xDB] (fun s => s.RIP = 0x12a496) (subR32R32Effect 0x12a496 3 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a496 3 11 3).toInstrSpec (sub_r32_r32_rex_effect_step 0x12a496 0x41 0xdb (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a499 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x12a499 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x12a499 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a499 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x12a499 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12a499 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12a49d [0x66, 0x42, 0x89, 0x44, 0x15, 0xE0] (StorePre 0x12a49d 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe0)) s (0x12a49d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12a49d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0)))
      [.gpr 0, .gpr 5, .gpr 10] [] [.rip] :=
    (movM16R16Effect_footprint 0x12a49d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0))).toInstrSpec (mov_m16_r16_rex_effect_step 0x12a49d 0x42 (by decide) 0 (.sib 5 (some 10) 0 (.d8 0xe0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x12a4a3 [0x41, 0x0F, 0xB7, 0xC3] (fun s => s.RIP = 0x12a4a3) (movzxR32R16Effect 0x12a4a3 4 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movzxR32R16Effect_footprint 0x12a4a3 4 0 11).toInstrSpec (movzx_r32_r16_rex_effect_step 0x12a4a3 0x41 (by decide) 0xc3 (by decide)) pre_rip
  have f14 : InstrSpec 0x12a4a7 [0x0F, 0xB7, 0x04, 0x47] (LoadPre 0x12a4a7 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x12a4a7 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a4a7 4 0 (.sib 7 (some 0) 1 .none))
      [.gpr 7, .gpr 0] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x12a4a7 4 0 (.sib 7 (some 0) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12a4a7 0 (.sib 7 (some 0) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x12a4ab [0x66, 0x42, 0x89, 0x44, 0x15, 0xE2] (StorePre 0x12a4ab 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe2)) s (0x12a4ab + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12a4ab 6 0 (.sib 5 (some 10) 0 (.d8 0xe2)))
      [.gpr 0, .gpr 5, .gpr 10] [] [.rip] :=
    (movM16R16Effect_footprint 0x12a4ab 6 0 (.sib 5 (some 10) 0 (.d8 0xe2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x12a4ab 0x42 (by decide) 0 (.sib 5 (some 10) 0 (.d8 0xe2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x12a4b1 [0x49, 0x8D, 0x42, 0xFC] (fun s => s.RIP = 0x12a4b1) (leaR64Effect 0x12a4b1 0 (.base 10 (.d8 0xfc)))
      [.gpr 10] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x12a4b1 0 (.base 10 (.d8 0xfc))).toInstrSpec (lea_r64_effect_step 0x12a4b1 0x49 (by decide) 0 (.base 10 (.d8 0xfc)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x12a4b5 [0x48, 0x81, 0xF9, 0x7F, 0x96, 0x98, 0x00] (fun s => s.RIP = 0x12a4b5) (cmpR64Imm32Effect 0x12a4b5 1 0x98967f)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR64Imm32Effect_footprint 0x12a4b5 1 0x98967f).toInstrSpec (cmp_r64_imm32_effect_step 0x12a4b5 0x48 0xf9 0x98967f (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x12a4bc [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a4bc) (movR64R64Effect 0x12a4bc 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a4bc 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a4bc 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a473) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a476) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a479) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a47d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a483) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a486) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a489) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a490) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 59), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a493) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a496) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a499) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a49d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4a3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4a7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4ab) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4b1) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4b5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f17 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 83), (1, 1), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4bc) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 83), (1, 88), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4bf) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel8_effect_step 0x12a4bf 7 0xaf) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a470 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a470 :=
  Rest.liftedBlock (rest_l12a470 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a470 x hx)

theorem rest_l12a4c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4c1 bytes_l12a4c1) (entryMap (live .l12a4c1))
      2 0x12a4c1 bytes_l12a4c1 b_l12a4c1 := by
  have f0 : InstrSpec 0x12a4c1 [0x48, 0x83, 0xFA, 0x09] (fun s => s.RIP = 0x12a4c1) (cmpR64Imm8Effect 0x12a4c1 2 0x9)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x12a4c1 2 0x9).toInstrSpec (cmp_r64_imm8_effect_step 0x12a4c1 0x48 0xfa 0x9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4c5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel8_effect_step 0x12a4c5 6 0x2b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a4c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4c1 :=
  Rest.liftedBlock (rest_l12a4c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4c1 x hx)

theorem rest_l12a4c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4c7 bytes_l12a4c7) (entryMap (live .l12a4c7))
      12 0x12a4c7 bytes_l12a4c7 b_l12a4c7 := by
  have f0 : InstrSpec 0x12a4c7 [0x89, 0xD1] (fun s => s.RIP = 0x12a4c7) (movR32R32Effect 0x12a4c7 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12a4c7 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x12a4c7 0xd1 (by decide)) pre_rip
  have f1 : InstrSpec 0x12a4c9 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x12a4c9) (shrR32Effect 0x12a4c9 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a4c9 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x12a4c9 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a4cc [0x0F, 0xB7, 0xC9] (fun s => s.RIP = 0x12a4cc) (movzxR32R16Effect 0x12a4cc 3 1 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movzxR32R16Effect_footprint 0x12a4cc 3 1 1).toInstrSpec (movzx_r32_r16_effect_step 0x12a4cc 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x12a4cf [0x69, 0xC9, 0x7B, 0x14, 0x00, 0x00] (fun s => s.RIP = 0x12a4cf) (imulR32R32Imm32Effect 0x12a4cf 6 1 1 0x147b)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x12a4cf 6 1 1 0x147b).toInstrSpec (imul_r32_r32_imm32_effect_step 0x12a4cf 0xc9 (by decide) 0x147b) pre_rip
  have f4 : InstrSpec 0x12a4d5 [0xC1, 0xE9, 0x11] (fun s => s.RIP = 0x12a4d5) (shrR32Effect 0x12a4d5 3 1 17)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a4d5 3 1 17).toInstrSpec (shr_r32_imm8_effect_step 0x12a4d5 0xe9 0x11 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a4d8 [0x44, 0x6B, 0xC9, 0x64] (fun s => s.RIP = 0x12a4d8) (imulR32R32Imm8Effect 0x12a4d8 4 9 1 0x64)
      [.gpr 1] [] [.reg 9, .flags, .rip] :=
    (imulR32R32Imm8Effect_footprint 0x12a4d8 4 9 1 0x64).toInstrSpec (imul_r32_r32_imm8_rex_effect_step 0x12a4d8 0x44 (by decide) 0xc9 (by decide) 0x64) pre_rip
  have f6 : InstrSpec 0x12a4dc [0x44, 0x29, 0xCA] (fun s => s.RIP = 0x12a4dc) (subR32R32Effect 0x12a4dc 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a4dc 3 2 9).toInstrSpec (sub_r32_r32_rex_effect_step 0x12a4dc 0x44 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a4df [0x0F, 0xB7, 0xD2] (fun s => s.RIP = 0x12a4df) (movzxR32R16Effect 0x12a4df 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R16Effect_footprint 0x12a4df 3 2 2).toInstrSpec (movzx_r32_r16_effect_step 0x12a4df 0xd2 (by decide)) pre_rip
  have f8 : InstrSpec 0x12a4e2 [0x0F, 0xB7, 0x14, 0x57] (LoadPre 0x12a4e2 (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x12a4e2 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a4e2 4 2 (.sib 7 (some 2) 1 .none))
      [.gpr 7, .gpr 2] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x12a4e2 4 2 (.sib 7 (some 2) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x12a4e2 2 (.sib 7 (some 2) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x12a4e6 [0x66, 0x89, 0x54, 0x05, 0xE2] (StorePre 0x12a4e6 5 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe2)) s (0x12a4e6 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x12a4e6 5 2 (.sib 5 (some 0) 0 (.d8 0xe2)))
      [.gpr 2, .gpr 5, .gpr 0] [] [.rip] :=
    (movM16R16Effect_footprint 0x12a4e6 5 2 (.sib 5 (some 0) 0 (.d8 0xe2))).toInstrSpec (mov_m16_r16_effect_step 0x12a4e6 2 (.sib 5 (some 0) 0 (.d8 0xe2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x12a4eb [0x48, 0x83, 0xC0, 0xFE] (fun s => s.RIP = 0x12a4eb) (addR64Imm8Effect 0x12a4eb 0 0xfe)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a4eb 0 0xfe).toInstrSpec (add_r64_imm8_effect_step 0x12a4eb 0x48 0xc0 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a4ef [0x48, 0x89, 0xCA] (fun s => s.RIP = 0x12a4ef) (movR64R64Effect 0x12a4ef 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a4ef 2 1).toInstrSpec (mov_r64_r64_effect_step 0x12a4ef 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4c9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4cc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4cf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4d5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4d8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4dc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 61), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4df) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 61), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4e2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4e6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4eb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 61), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4ef) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 61), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4f2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l12a4c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4c7 :=
  Rest.liftedBlock (rest_l12a4c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4c7 x hx)

theorem rest_l12a4f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4f2 bytes_l12a4f2) (entryMap (live .l12a4f2))
      2 0x12a4f2 bytes_l12a4f2 b_l12a4f2 := by
  have f0 : InstrSpec 0x12a4f2 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x12a4f2) (testR64R64Effect 0x12a4f2 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12a4f2 8 8).toInstrSpec (test_r64_r64_effect_step 0x12a4f2 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a4f5 4 0x5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a4f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4f2 :=
  Rest.liftedBlock (rest_l12a4f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4f2 x hx)

theorem rest_l12a4f7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4f7 bytes_l12a4f7) (entryMap (live .l12a4f7))
      2 0x12a4f7 bytes_l12a4f7 b_l12a4f7 := by
  have f0 : InstrSpec 0x12a4f7 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x12a4f7) (testR64R64Effect 0x12a4f7 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12a4f7 2 2).toInstrSpec (test_r64_r64_effect_step 0x12a4f7 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a4fa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a4fa 4 0xc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a4f7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4f7 :=
  Rest.liftedBlock (rest_l12a4f7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4f7 x hx)

theorem rest_l12a4fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a4fc bytes_l12a4fc) (entryMap (live .l12a4fc))
      3 0x12a4fc bytes_l12a4fc b_l12a4fc := by
  have f0 : InstrSpec 0x12a4fc [0x0F, 0xB6, 0x4C, 0x57, 0x01] (LoadPre 0x12a4fc (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1)) s (0x12a4fc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12a4fc 5 1 (.sib 7 (some 2) 1 (.d8 0x1)))
      [.gpr 7, .gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x12a4fc 5 1 (.sib 7 (some 2) 1 (.d8 0x1))).toInstrSpec (movzx_r32_m8_effect_step 0x12a4fc 1 (.sib 7 (some 2) 1 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a501 [0x88, 0x4C, 0x05, 0xE3] (StorePre 0x12a501 4 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe3)) s (0x12a501 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12a501 4 1 (.sib 5 (some 0) 0 (.d8 0xe3)))
      [.gpr 1, .gpr 5, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x12a501 4 1 (.sib 5 (some 0) 0 (.d8 0xe3))).toInstrSpec (mov_m8_r8_effect_step 0x12a501 1 (by decide) (.sib 5 (some 0) 0 (.d8 0xe3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12a505 [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x12a505) (decR64Effect 0x12a505 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x12a505 0).toInstrSpec (dec_r64_effect_step 0x12a505 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a501) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a505) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a508) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l12a4fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a4fc :=
  Rest.liftedBlock (rest_l12a4fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a4fc x hx)

theorem rest_l12a508 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a508 bytes_l12a508) (entryMap (live .l12a508))
      9 0x12a508 bytes_l12a508 b_l12a508 := by
  have f0 : InstrSpec 0x12a508 [0x41, 0xB9, 0x14, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a508) (movR32Imm32Effect 0x12a508 6 9 0x14)
      [] [] [.reg 9, .rip] :=
    (movR32Imm32Effect_footprint 0x12a508 6 9 0x14).toInstrSpec (mov_r32_imm32_rex_effect_step 0x12a508 0x41 0xb9 (by decide) (by decide) 0x14) pre_rip
  have f1 : InstrSpec 0x12a50e [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x12a50e) (subR64R64Effect 0x12a50e 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x12a50e 9 0).toInstrSpec (sub_r64_r64_effect_step 0x12a50e 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a511 [0x4C, 0x8D, 0x04, 0x28] (fun s => s.RIP = 0x12a511) (leaR64Effect 0x12a511 8 (.sib 0 (some 5) 0 .none))
      [.gpr 0, .gpr 5] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x12a511 8 (.sib 0 (some 5) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a511 0x4c (by decide) 0 (.sib 0 (some 5) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a515 [0x49, 0x83, 0xC0, 0xE4] (fun s => s.RIP = 0x12a515) (addR64Imm8Effect 0x12a515 8 0xe4)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a515 8 0xe4).toInstrSpec (add_r64_imm8_effect_step 0x12a515 0x49 0xc0 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a519 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a519) (movR32Imm32Effect 0x12a519 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x12a519 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12a519 0xba (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x12a51e [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x12a51e) (movR64R64Effect 0x12a51e 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12a51e 7 6).toInstrSpec (mov_r64_r64_effect_step 0x12a51e 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12a521 [0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a521) (movR32Imm32Effect 0x12a521 5 6 0x1)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x12a521 5 6 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x12a521 0xbe (by decide) 0x1) pre_rip
  have f7 : InstrSpec 0x12a526 [0x31, 0xC9] (fun s => s.RIP = 0x12a526) (xorR32R32Effect 0x12a526 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a526 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x12a526 0xc9 (by decide)) pre_rip
  have f8 : InstrSpec 0x12a528 [0xFF, 0x15, 0xBA, 0x98, 0x0D, 0x00] (GoesTo (CallMemPre 0x12a528 (.rip 0xd98ba)) (callEffect (callMemPtr 0x12a528 (.rip 0xd98ba)) (0x12a528 + BitVec.ofNat 64 (callMemLen (.rip 0xd98ba)))) 0x128b20) (callEffect (callMemPtr 0x12a528 (.rip 0xd98ba)) (0x12a528 + BitVec.ofNat 64 (callMemLen (.rip 0xd98ba))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x12a528 (.rip 0xd98ba)).toInstrSpec (call_m64_effect_step 0x12a528 (.rip 0xd98ba) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x128b20
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a50e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a511) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 57), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a515) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a519) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a51e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a521) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a526) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 4), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a528) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 61), (3, 3), (4, 69), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128b20) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l12a508 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a508 :=
  Rest.liftedBlock (rest_l12a508 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a508 x hx)

theorem rest_l12a52e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a52e bytes_l12a52e) (entryMap (live .l12a52e))
      4 0x12a52e bytes_l12a52e b_l12a52e := by
  have f0 : InstrSpec 0x12a52e [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x12a52e) (addR64Imm8Effect 0x12a52e 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a52e 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x12a52e 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a532 [0x5B] (PopPre 0x12a532) (popR64Effect 0x12a532 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a532 1 3).toInstrSpec (pop_r64_effect_step 0x12a532 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x12a533 [0x5D] (PopPre 0x12a533) (popR64Effect 0x12a533 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12a533 1 5).toInstrSpec (pop_r64_effect_step 0x12a533 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x12a534 [0xC3] (RetPre 0x12a534) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a534).toInstrSpec (ret_effect_step 0x12a534) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a532) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a533) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a534) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l12a52e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a52e :=
  Rest.liftedBlock (rest_l12a52e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a52e x hx)

theorem rest_l12a700_1 [Bindings] (code : CodeMap) :
    Rest (n := 94) code lifted (codeRange 0x12a700 bytes_l12a700) [(0, 92), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x12a744 bytes_l12a700_1 b_l12a700_1 := by
  have f20 : InstrSpec 0x12a744 [0xC3] (RetPre 0x12a744) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a744).toInstrSpec (ret_effect_step 0x12a744) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f20 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 95) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 96) (ρ' := [(0, 92), (1, 90), (2, 55), (3, 3), (4, 95), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f20 (by decide) rfl rfl rfl (by decide)

theorem rest_l12a700 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a700 bytes_l12a700) (entryMap (live .l12a700))
      21 0x12a700 bytes_l12a700 b_l12a700 := by
  have f0 : InstrSpec 0x12a700 [0x49, 0x89, 0xD0] (fun s => s.RIP = 0x12a700) (movR64R64Effect 0x12a700 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x12a700 8 2).toInstrSpec (mov_r64_r64_effect_step 0x12a700 0x49 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a703 [0x48, 0x89, 0xFA] (fun s => s.RIP = 0x12a703) (movR64R64Effect 0x12a703 2 7)
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a703 2 7).toInstrSpec (mov_r64_r64_effect_step 0x12a703 0x48 0xfa (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a706 [0x40, 0x0F, 0xB6, 0xCE] (fun s => s.RIP = 0x12a706) (movzxR32R8Effect 0x12a706 4 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x12a706 4 1 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12a706 0x40 (by decide) 0xce (by decide)) pre_rip
  have f3 : InstrSpec 0x12a70a [0x48, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01] (fun s => s.RIP = 0x12a70a) (movR64Imm64Effect 0x12a70a 0 0x101010101010101)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x12a70a 0 0x101010101010101).toInstrSpec (mov_r64_imm64_effect_step 0x12a70a 0x48 0xb8 (by decide) (by decide) 0x101010101010101) pre_rip
  have f4 : InstrSpec 0x12a714 [0x48, 0x0F, 0xAF, 0xC1] (fun s => s.RIP = 0x12a714) (imulR64R64Effect 0x12a714 4 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (imulR64R64Effect_footprint 0x12a714 4 0 1).toInstrSpec (imul_r64_r64_effect_step 0x12a714 0x48 (by decide) 0xc1 (by decide)) pre_rip
  have f5 : InstrSpec 0x12a718 [0x89, 0xD1] (fun s => s.RIP = 0x12a718) (movR32R32Effect 0x12a718 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x12a718 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x12a718 0xd1 (by decide)) pre_rip
  have f6 : InstrSpec 0x12a71a [0xF7, 0xD9] (fun s => s.RIP = 0x12a71a) (negR32Effect 0x12a71a 2 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR32Effect_footprint 0x12a71a 2 1).toInstrSpec (neg_r32_effect_step 0x12a71a 0xd9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a71c [0x83, 0xE1, 0x07] (fun s => s.RIP = 0x12a71c) (andR32Imm8Effect 0x12a71c 3 1 0x7)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a71c 3 1 0x7).toInstrSpec (and_r32_imm8_effect_step 0x12a71c 0xe1 0x7 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x12a71f [0x49, 0x39, 0xC8] (fun s => s.RIP = 0x12a71f) (cmpR64R64Effect 0x12a71f 8 1)
      [.gpr 8, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a71f 8 1).toInstrSpec (cmp_r64_r64_effect_step 0x12a71f 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12a722 [0x49, 0x0F, 0x42, 0xC8] (fun s => s.RIP = 0x12a722) (atFlags (condHolds 2) (cmovR64R64Effect 0x12a722 4 1 8))
      [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x12a722 4 1 8 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x12a722 2 0x49 (by decide) 0xc8 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x12a726 [0x49, 0x29, 0xC8] (fun s => s.RIP = 0x12a726) (subR64R64Effect 0x12a726 8 1)
      [.gpr 8, .gpr 1] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x12a726 8 1).toInstrSpec (sub_r64_r64_effect_step 0x12a726 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a729 [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x12a729) (movR64R64Effect 0x12a729 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12a729 6 8).toInstrSpec (mov_r64_r64_effect_step 0x12a729 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x12a72c [0x48, 0xC1, 0xEE, 0x03] (fun s => s.RIP = 0x12a72c) (shrR64Effect 0x12a72c 4 6 3)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a72c 4 6 3).toInstrSpec (shr_r64_imm8_effect_step 0x12a72c 0x48 0xee 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x12a730 [0x41, 0x83, 0xE0, 0x07] (fun s => s.RIP = 0x12a730) (andR32Imm8Effect 0x12a730 4 8 0x7)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a730 4 8 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x12a730 0x41 0xe0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x12a734 [0xF3, 0xAA] (RepPre 0x12a734 (RepStosbPre 0x12a734)) (repStosbEffect 0x12a734)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosbEffect_footprint 0x12a734).toInstrSpecOfRuns (rep_stosb_runs hstride 0x12a734) (RepStosOk.of_stateOf RepStosbPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x12a736 [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x12a736) (movR64R64Effect 0x12a736 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a736 1 6).toInstrSpec (mov_r64_r64_effect_step 0x12a736 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x12a739 [0xF3, 0x48, 0xAB] (RepPre 0x12a739 (RepStosqPre 0x12a739)) (repStosqEffect 0x12a739)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosqEffect_footprint 0x12a739).toInstrSpecOfRuns (rep_stosq_runs hstride 0x12a739 0x48 (by decide)) (RepStosOk.of_stateOf RepStosqPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f17 : InstrSpec 0x12a73c [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x12a73c) (movR64R64Effect 0x12a73c 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a73c 1 8).toInstrSpec (mov_r64_r64_effect_step 0x12a73c 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x12a73f [0xF3, 0xAA] (RepPre 0x12a73f (RepStosbPre 0x12a73f)) (repStosbEffect 0x12a73f)
      [.gpr 0, .gpr 7, .gpr 1, .df] [] [.reg 7, .reg 1, .rip] :=
    (repStosbEffect_footprint 0x12a73f).toInstrSpecOfRuns (rep_stosb_runs hstride 0x12a73f) (RepStosOk.of_stateOf RepStosbPre.iff (by lift_reads) (by lift_reads) (by lift_reads))
  have f19 : InstrSpec 0x12a741 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x12a741) (movR64R64Effect 0x12a741 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a741 0 2).toInstrSpec (mov_r64_r64_effect_step 0x12a741 0x48 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a703) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a706) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a70a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a714) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a718) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a71a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 65), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a71c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 67), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a71f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 67), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a722) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a726) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a729) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 75), (7, 7), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a72c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 7), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a730) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 71), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 7), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a734) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a736) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 61), (1, 83), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a739) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 61), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 85), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a73c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 61), (1, 87), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 85), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a73f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 90) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 91) (ρ' := [(0, 61), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a741) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 90), (2, 55), (3, 3), (4, 4), (5, 5), (6, 77), (7, 89), (8, 79), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a744) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12a700_1 code

theorem block_l12a700 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a700 :=
  Rest.liftedBlock (rest_l12a700 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a700 x hx)

theorem rest_l12a820 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a820 bytes_l12a820) (entryMap (live .l12a820))
      16 0x12a820 bytes_l12a820 b_l12a820 := by
  have f0 : InstrSpec 0x12a820 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x12a820) (movR64R64Effect 0x12a820 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x12a820 0 7).toInstrSpec (mov_r64_r64_effect_step 0x12a820 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a823 [0x41, 0x89, 0xC0] (fun s => s.RIP = 0x12a823) (movR32R32Effect 0x12a823 3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x12a823 3 8 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x12a823 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a826 [0x41, 0xF7, 0xD8] (fun s => s.RIP = 0x12a826) (negR32Effect 0x12a826 3 8)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (negR32Effect_footprint 0x12a826 3 8).toInstrSpec (neg_r32_rex_effect_step 0x12a826 0x41 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a829 [0x41, 0x83, 0xE0, 0x07] (fun s => s.RIP = 0x12a829) (andR32Imm8Effect 0x12a829 4 8 0x7)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a829 4 8 0x7).toInstrSpec (and_r32_imm8_rex_effect_step 0x12a829 0x41 0xe0 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a82d [0x4C, 0x39, 0xC2] (fun s => s.RIP = 0x12a82d) (cmpR64R64Effect 0x12a82d 2 8)
      [.gpr 2, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a82d 2 8).toInstrSpec (cmp_r64_r64_effect_step 0x12a82d 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12a830 [0x4C, 0x0F, 0x42, 0xC2] (fun s => s.RIP = 0x12a830) (atFlags (condHolds 2) (cmovR64R64Effect 0x12a830 4 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x12a830 4 8 2 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x12a830 2 0x4c (by decide) 0xc2 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x12a834 [0x4C, 0x89, 0xC1] (fun s => s.RIP = 0x12a834) (movR64R64Effect 0x12a834 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a834 1 8).toInstrSpec (mov_r64_r64_effect_step 0x12a834 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x12a837 [0xF3, 0xA4] (RepPre 0x12a837 (RepMovsbPre 0x12a837)) (repMovsbEffect 0x12a837)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x12a837).toInstrSpecOfRuns (rep_movsb_runs hstride 0x12a837) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f8 : InstrSpec 0x12a839 [0x4C, 0x29, 0xC2] (fun s => s.RIP = 0x12a839) (subR64R64Effect 0x12a839 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x12a839 2 8).toInstrSpec (sub_r64_r64_effect_step 0x12a839 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12a83c [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a83c) (movR64R64Effect 0x12a83c 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a83c 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a83c 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12a83f [0x48, 0xC1, 0xE9, 0x03] (fun s => s.RIP = 0x12a83f) (shrR64Effect 0x12a83f 4 1 3)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a83f 4 1 3).toInstrSpec (shr_r64_imm8_effect_step 0x12a83f 0x48 0xe9 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12a843 [0xF3, 0x48, 0xA5] (RepPre 0x12a843 (RepMovsqPre 0x12a843)) (repMovsqEffect 0x12a843)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x12a843).toInstrSpecOfRuns (rep_movsq_runs hstride 0x12a843 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f12 : InstrSpec 0x12a846 [0x83, 0xE2, 0x07] (fun s => s.RIP = 0x12a846) (andR32Imm8Effect 0x12a846 3 2 0x7)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a846 3 2 0x7).toInstrSpec (and_r32_imm8_effect_step 0x12a846 0xe2 0x7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x12a849 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x12a849) (movR64R64Effect 0x12a849 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x12a849 1 2).toInstrSpec (mov_r64_r64_effect_step 0x12a849 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x12a84c [0xF3, 0xA4] (RepPre 0x12a84c (RepMovsbPre 0x12a84c)) (repMovsbEffect 0x12a84c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsbEffect_footprint 0x12a84c).toInstrSpecOfRuns (rep_movsb_runs hstride 0x12a84c) (RepMovsOk.of_stateOf RepMovsbPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f15 : InstrSpec 0x12a84e [0xC3] (RetPre 0x12a84e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a84e).toInstrSpec (ret_effect_step 0x12a84e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a823) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a826) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a829) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a82d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a830) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a834) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a837) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a839) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a83c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a83f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 74), (2, 70), (3, 3), (4, 4), (5, 5), (6, 67), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a843) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (2, 70), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a846) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a849) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 81), (2, 79), (3, 3), (4, 4), (5, 5), (6, 76), (7, 77), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a84c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.out (n := 85) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 86) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 4), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a84e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f15 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 89) (ρ' := [(0, 53), (1, 85), (2, 79), (3, 3), (4, 88), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f15 (by decide) rfl rfl rfl (by decide)

theorem block_l12a820 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a820 :=
  Rest.liftedBlock (rest_l12a820 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a820 x hx)

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

theorem_by block_l100a20_eval :
    program.runBlock (dialect code) ⟨.l100a20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101dd0_eval :
    program.runBlock (dialect code) ⟨.l101dd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101dea_eval :
    program.runBlock (dialect code) ⟨.l101dea, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101df8_eval :
    program.runBlock (dialect code) ⟨.l101df8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e0c_eval :
    program.runBlock (dialect code) ⟨.l101e0c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e20_eval :
    program.runBlock (dialect code) ⟨.l101e20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e4c_eval :
    program.runBlock (dialect code) ⟨.l101e4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101e62_eval :
    program.runBlock (dialect code) ⟨.l101e62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1148d0_eval :
    program.runBlock (dialect code) ⟨.l1148d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124290_eval :
    program.runBlock (dialect code) ⟨.l124290, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1242a3_eval :
    program.runBlock (dialect code) ⟨.l1242a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1242e0_eval :
    program.runBlock (dialect code) ⟨.l1242e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1242ed_eval :
    program.runBlock (dialect code) ⟨.l1242ed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12430f_eval :
    program.runBlock (dialect code) ⟨.l12430f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124322_eval :
    program.runBlock (dialect code) ⟨.l124322, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12432b_eval :
    program.runBlock (dialect code) ⟨.l12432b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124411_eval :
    program.runBlock (dialect code) ⟨.l124411, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124414_eval :
    program.runBlock (dialect code) ⟨.l124414, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12441a_eval :
    program.runBlock (dialect code) ⟨.l12441a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124ae0_eval :
    program.runBlock (dialect code) ⟨.l124ae0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124af7_eval :
    program.runBlock (dialect code) ⟨.l124af7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b13_eval :
    program.runBlock (dialect code) ⟨.l124b13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b35_eval :
    program.runBlock (dialect code) ⟨.l124b35, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b3e_eval :
    program.runBlock (dialect code) ⟨.l124b3e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b4e_eval :
    program.runBlock (dialect code) ⟨.l124b4e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b50_eval :
    program.runBlock (dialect code) ⟨.l124b50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124b90_eval :
    program.runBlock (dialect code) ⟨.l124b90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l124bcf_eval :
    program.runBlock (dialect code) ⟨.l124bcf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127670_eval :
    program.runBlock (dialect code) ⟨.l127670, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127690_eval :
    program.runBlock (dialect code) ⟨.l127690, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12769c_eval :
    program.runBlock (dialect code) ⟨.l12769c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1276aa_eval :
    program.runBlock (dialect code) ⟨.l1276aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1276d0_eval :
    program.runBlock (dialect code) ⟨.l1276d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1276d8_eval :
    program.runBlock (dialect code) ⟨.l1276d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1276fa_eval :
    program.runBlock (dialect code) ⟨.l1276fa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127704_eval :
    program.runBlock (dialect code) ⟨.l127704, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12770a_eval :
    program.runBlock (dialect code) ⟨.l12770a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12771b_eval :
    program.runBlock (dialect code) ⟨.l12771b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127726_eval :
    program.runBlock (dialect code) ⟨.l127726, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127b80_eval :
    program.runBlock (dialect code) ⟨.l127b80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127b89_eval :
    program.runBlock (dialect code) ⟨.l127b89, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127b9e_eval :
    program.runBlock (dialect code) ⟨.l127b9e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bad_eval :
    program.runBlock (dialect code) ⟨.l127bad, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bd3_eval :
    program.runBlock (dialect code) ⟨.l127bd3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bdd_eval :
    program.runBlock (dialect code) ⟨.l127bdd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127be1_eval :
    program.runBlock (dialect code) ⟨.l127be1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bf9_eval :
    program.runBlock (dialect code) ⟨.l127bf9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127bfd_eval :
    program.runBlock (dialect code) ⟨.l127bfd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c04_eval :
    program.runBlock (dialect code) ⟨.l127c04, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c0d_eval :
    program.runBlock (dialect code) ⟨.l127c0d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c1e_eval :
    program.runBlock (dialect code) ⟨.l127c1e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c36_eval :
    program.runBlock (dialect code) ⟨.l127c36, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c41_eval :
    program.runBlock (dialect code) ⟨.l127c41, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c50_eval :
    program.runBlock (dialect code) ⟨.l127c50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c5f_eval :
    program.runBlock (dialect code) ⟨.l127c5f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127c7e_eval :
    program.runBlock (dialect code) ⟨.l127c7e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127d50_eval :
    program.runBlock (dialect code) ⟨.l127d50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a40_eval :
    program.runBlock (dialect code) ⟨.l128a40, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a4c_eval :
    program.runBlock (dialect code) ⟨.l128a4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a52_eval :
    program.runBlock (dialect code) ⟨.l128a52, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a63_eval :
    program.runBlock (dialect code) ⟨.l128a63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a69_eval :
    program.runBlock (dialect code) ⟨.l128a69, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a6f_eval :
    program.runBlock (dialect code) ⟨.l128a6f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a8b_eval :
    program.runBlock (dialect code) ⟨.l128a8b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a96_eval :
    program.runBlock (dialect code) ⟨.l128a96, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ab2_eval :
    program.runBlock (dialect code) ⟨.l128ab2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ab5_eval :
    program.runBlock (dialect code) ⟨.l128ab5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ab9_eval :
    program.runBlock (dialect code) ⟨.l128ab9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128abe_eval :
    program.runBlock (dialect code) ⟨.l128abe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128ad0_eval :
    program.runBlock (dialect code) ⟨.l128ad0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128af3_eval :
    program.runBlock (dialect code) ⟨.l128af3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129560_eval :
    program.runBlock (dialect code) ⟨.l129560, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129594_eval :
    program.runBlock (dialect code) ⟨.l129594, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129770_eval :
    program.runBlock (dialect code) ⟨.l129770, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12979c_eval :
    program.runBlock (dialect code) ⟨.l12979c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c30_eval :
    program.runBlock (dialect code) ⟨.l129c30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c4c_eval :
    program.runBlock (dialect code) ⟨.l129c4c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c56_eval :
    program.runBlock (dialect code) ⟨.l129c56, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c5e_eval :
    program.runBlock (dialect code) ⟨.l129c5e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c63_eval :
    program.runBlock (dialect code) ⟨.l129c63, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c7b_eval :
    program.runBlock (dialect code) ⟨.l129c7b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c7d_eval :
    program.runBlock (dialect code) ⟨.l129c7d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129c90_eval :
    program.runBlock (dialect code) ⟨.l129c90, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129cd0_eval :
    program.runBlock (dialect code) ⟨.l129cd0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129ce7_eval :
    program.runBlock (dialect code) ⟨.l129ce7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129d13_eval :
    program.runBlock (dialect code) ⟨.l129d13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129d23_eval :
    program.runBlock (dialect code) ⟨.l129d23, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129d39_eval :
    program.runBlock (dialect code) ⟨.l129d39, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l129d5f_eval :
    program.runBlock (dialect code) ⟨.l129d5f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a050_eval :
    program.runBlock (dialect code) ⟨.l12a050, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a070_eval :
    program.runBlock (dialect code) ⟨.l12a070, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a100_eval :
    program.runBlock (dialect code) ⟨.l12a100, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a430_eval :
    program.runBlock (dialect code) ⟨.l12a430, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a454_eval :
    program.runBlock (dialect code) ⟨.l12a454, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a470_eval :
    program.runBlock (dialect code) ⟨.l12a470, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4c1_eval :
    program.runBlock (dialect code) ⟨.l12a4c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4c7_eval :
    program.runBlock (dialect code) ⟨.l12a4c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4f2_eval :
    program.runBlock (dialect code) ⟨.l12a4f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4f7_eval :
    program.runBlock (dialect code) ⟨.l12a4f7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a4fc_eval :
    program.runBlock (dialect code) ⟨.l12a4fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a508_eval :
    program.runBlock (dialect code) ⟨.l12a508, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a52e_eval :
    program.runBlock (dialect code) ⟨.l12a52e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a700_eval :
    program.runBlock (dialect code) ⟨.l12a700, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a820_eval :
    program.runBlock (dialect code) ⟨.l12a820, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Sec1.LIR
