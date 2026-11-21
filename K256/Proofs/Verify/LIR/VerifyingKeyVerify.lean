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

theorem rest_l102fc0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102fc0 bytes_l102fc0) (entryMap (live .l102fc0))
      12 0x102fc0 bytes_l102fc0 b_l102fc0 := by
  have f0 : InstrSpec 0x102fc0 [0x41, 0x57] (PushPre 0x102fc0 2) (pushR64Effect 0x102fc0 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102fc0 2 15).toInstrSpec (push_r64_rex_effect_step 0x102fc0 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x102fc2 [0x41, 0x56] (PushPre 0x102fc2 2) (pushR64Effect 0x102fc2 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102fc2 2 14).toInstrSpec (push_r64_rex_effect_step 0x102fc2 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102fc4 [0x41, 0x54] (PushPre 0x102fc4 2) (pushR64Effect 0x102fc4 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102fc4 2 12).toInstrSpec (push_r64_rex_effect_step 0x102fc4 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102fc6 [0x53] (PushPre 0x102fc6 1) (pushR64Effect 0x102fc6 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102fc6 1 3).toInstrSpec (push_r64_effect_step 0x102fc6 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102fc7 [0x48, 0x81, 0xEC, 0xF8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102fc7) (subR64Imm32Effect 0x102fc7 4 0x1f8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x102fc7 4 0x1f8).toInstrSpec (sub_r64_imm32_effect_step 0x102fc7 0x48 0xec 0x1f8 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102fce [0x49, 0x89, 0xCF] (fun s => s.RIP = 0x102fce) (movR64R64Effect 0x102fce 15 1)
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x102fce 15 1).toInstrSpec (mov_r64_r64_effect_step 0x102fce 0x49 0xcf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102fd1 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x102fd1) (movR64R64Effect 0x102fd1 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x102fd1 3 2).toInstrSpec (mov_r64_r64_effect_step 0x102fd1 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102fd4 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x102fd4) (movR64R64Effect 0x102fd4 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102fd4 14 6).toInstrSpec (mov_r64_r64_effect_step 0x102fd4 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102fd7 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x102fd7) (movR64R64Effect 0x102fd7 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102fd7 6 7).toInstrSpec (mov_r64_r64_effect_step 0x102fd7 0x48 0xfe (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102fda [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x102fda) (leaR64Effect 0x102fda 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102fda 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x102fda 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x102fdf [0xBA, 0x41, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102fdf) (movR32Imm32Effect 0x102fdf 5 2 0x41)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x102fdf 5 2 0x41).toInstrSpec (mov_r32_imm32_effect_step 0x102fdf 0xba (by decide) 0x41) pre_rip
  have f11 : InstrSpec 0x102fe4 [0xE8, 0xA7, 0x33, 0x00, 0x00] (PushPre 0x102fe4 5) (callEffect (fun _ => 0x106390) 0x102fe9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102fe4 0x106390 0x102fe9).toInstrSpec (call_rel32_effect_step 0x102fe4 0x33a7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fc7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fce) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fd1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fd4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fd7) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 61), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fda) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 61), (5, 5), (6, 69), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fdf) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 73), (3, 65), (4, 61), (5, 5), (6, 69), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fe4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 73), (3, 65), (4, 75), (5, 5), (6, 69), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106390) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 77) (by decide) (by decide) rfl rfl

theorem block_l102fc0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102fc0 :=
  Rest.liftedBlock (rest_l102fc0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102fc0 x hx)

theorem rest_l102fe9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102fe9 bytes_l102fe9) (entryMap (live .l102fe9))
      2 0x102fe9 bytes_l102fe9 b_l102fe9 := by
  have f0 : InstrSpec 0x102fe9 [0x80, 0x7C, 0x24, 0x08, 0x00] (LoadPre 0x102fe9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102fe9 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x102fe9 5 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x102fe9 5 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x102fe9 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102fee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x102fee 5 0x414) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102fe9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102fe9 :=
  Rest.liftedBlock (rest_l102fe9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102fe9 x hx)

theorem rest_l102ff4 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102ff4 bytes_l102ff4) (entryMap (live .l102ff4))
      12 0x102ff4 bytes_l102ff4 b_l102ff4 := by
  have f0 : InstrSpec 0x102ff4 [0x48, 0x8D, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x102ff4) (leaR64Effect 0x102ff4 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102ff4 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (lea_r64_effect_step 0x102ff4 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102ffc [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x102ffc) (leaR64Effect 0x102ffc 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102ffc 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102ffc 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103001 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103001) (movR32Imm32Effect 0x103001 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x103001 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x103001 0xb9 (by decide) 0xb) pre_rip
  have f3 : InstrSpec 0x103006 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x103006) (movR64R64Effect 0x103006 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103006 7 0).toInstrSpec (mov_r64_r64_effect_step 0x103006 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103009 [0xF3, 0x48, 0xA5] (RepPre 0x103009 (RepMovsqPre 0x103009)) (repMovsqEffect 0x103009)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x103009).toInstrSpecOfRuns (rep_movsq_runs hstride 0x103009 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x10300c [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10300c) (leaR64Effect 0x10300c 7 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10300c 7 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (lea_r64_effect_step 0x10300c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x103014 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103014) (movR32Imm32Effect 0x103014 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x103014 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x103014 0xb9 (by decide) 0xb) pre_rip
  have f7 : InstrSpec 0x103019 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x103019) (movR64R64Effect 0x103019 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103019 6 0).toInstrSpec (mov_r64_r64_effect_step 0x103019 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10301c [0xF3, 0x48, 0xA5] (RepPre 0x10301c (RepMovsqPre 0x10301c)) (repMovsqEffect 0x10301c)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10301c).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10301c 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f9 : InstrSpec 0x10301f [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x10301f) (leaR64Effect 0x10301f 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10301f 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10301f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x103024 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x103024) (movR64R64Effect 0x103024 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103024 6 15).toInstrSpec (mov_r64_r64_effect_step 0x103024 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x103027 [0xE8, 0x94, 0x0A, 0x00, 0x00] (PushPre 0x103027 5) (callEffect (fun _ => 0x103ac0) 0x10302c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103027 0x103ac0 0x10302c).toInstrSpec (call_rel32_effect_step 0x103027 0xa94 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ffc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103001) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103006) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103009) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10300c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103014) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103019) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 64), (3, 3), (4, 4), (5, 5), (6, 66), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10301c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10301f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103024) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (6, 71), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103027) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (3, 3), (4, 73), (5, 5), (6, 71), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103ac0) f11 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l102ff4 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102ff4 :=
  Rest.liftedBlock (rest_l102ff4 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102ff4 x hx)

theorem rest_l10302c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10302c bytes_l10302c) (entryMap (live .l10302c))
      2 0x10302c bytes_l10302c b_l10302c := by
  have f0 : InstrSpec 0x10302c [0x83, 0x7C, 0x24, 0x08, 0x01] (LoadPre 0x10302c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10302c + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x10302c 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x10302c 5 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x10302c (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103031) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x103031 4 0x3fb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10302c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10302c :=
  Rest.liftedBlock (rest_l10302c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10302c x hx)

theorem rest_l103037_1 [Bindings] (code : CodeMap) :
    Rest (n := 83) code lifted (codeRange 0x103037 bytes_l103037) [(0, 80), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x1030c3 bytes_l103037_1 b_l103037_1 := by
  have f20 : InstrSpec 0x1030c3 [0x48, 0xB8, 0x72, 0xF3, 0x6E, 0x3C, 0x3A, 0xF5, 0x4F, 0xA5] (fun s => s.RIP = 0x1030c3) (movR64Imm64Effect 0x1030c3 0 0xa54ff53a3c6ef372)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1030c3 0 0xa54ff53a3c6ef372).toInstrSpec (mov_r64_imm64_effect_step 0x1030c3 0x48 0xb8 (by decide) (by decide) 0xa54ff53a3c6ef372) pre_rip
  have f21 : InstrSpec 0x1030cd [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (StorePre 0x1030cd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1030cd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1030cd 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1030cd 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_m64_r64_effect_step 0x1030cd 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x1030d5 [0x48, 0xB8, 0x67, 0xE6, 0x09, 0x6A, 0x85, 0xAE, 0x67, 0xBB] (fun s => s.RIP = 0x1030d5) (movR64Imm64Effect 0x1030d5 0 0xbb67ae856a09e667)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1030d5 0 0xbb67ae856a09e667).toInstrSpec (mov_r64_imm64_effect_step 0x1030d5 0x48 0xb8 (by decide) (by decide) 0xbb67ae856a09e667) pre_rip
  have f23 : InstrSpec 0x1030df [0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (StorePre 0x1030df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1030df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1030df 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1030df 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_m64_r64_effect_step 0x1030df 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x1030e7 [0x48, 0xC7, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1030e7 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x1030e7 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1030e7 (.sib 4 none 0 (.d32 0x158)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1030e7 (.sib 4 none 0 (.d32 0x158)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1030e7 0x48 (by decide) (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x1030f3 [0xC6, 0x84, 0x24, 0x37, 0x01, 0x00, 0x00, 0x00] (StorePre 0x1030f3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x137)) s (0x1030f3 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x1030f3 (.sib 4 none 0 (.d32 0x137)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1030f3 (.sib 4 none 0 (.d32 0x137)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x1030f3 (.sib 4 none 0 (.d32 0x137)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x1030fb [0x48, 0x83, 0xFB, 0x3F] (fun s => s.RIP = 0x1030fb) (cmpR64Imm8Effect 0x1030fb 3 0x3f)
      [.gpr 3] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1030fb 3 0x3f).toInstrSpec (cmp_r64_imm8_effect_step 0x1030fb 0x48 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030cd) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 83), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030d5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030df) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030e7) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030f3) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030fb) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f26 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 92) f26 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 93) (ρ' := [(0, 86), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 91), (19, 92), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030ff) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 94) (jcc_rel8_effect_step 0x1030ff 7 0x1d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l103037 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103037 bytes_l103037) (entryMap (live .l103037))
      28 0x103037 bytes_l103037 b_l103037 := by
  have f0 : InstrSpec 0x103037 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x103037 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103037 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103037 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103037 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x103037 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10303c [0x48, 0x89, 0x84, 0x24, 0x98, 0x01, 0x00, 0x00] (StorePre 0x10303c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x198)) s (0x10303c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10303c 0 (.sib 4 none 0 (.d32 0x198)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10303c 0 (.sib 4 none 0 (.d32 0x198))).toInstrSpec (mov_m64_r64_effect_step 0x10303c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x198)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103044 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x103044 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103044 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103044 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103044 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x103044 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x103049 [0x48, 0x89, 0x84, 0x24, 0x90, 0x01, 0x00, 0x00] (StorePre 0x103049 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x190)) s (0x103049 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103049 0 (.sib 4 none 0 (.d32 0x190)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103049 0 (.sib 4 none 0 (.d32 0x190))).toInstrSpec (mov_m64_r64_effect_step 0x103049 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x190)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x103051 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x103051 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103051 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103051 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103051 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x103051 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103056 [0x48, 0x89, 0x84, 0x24, 0x88, 0x01, 0x00, 0x00] (StorePre 0x103056 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x188)) s (0x103056 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103056 0 (.sib 4 none 0 (.d32 0x188)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103056 0 (.sib 4 none 0 (.d32 0x188))).toInstrSpec (mov_m64_r64_effect_step 0x103056 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x188)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10305e [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x10305e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10305e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10305e 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10305e 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10305e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x103063 [0x48, 0x89, 0x84, 0x24, 0x80, 0x01, 0x00, 0x00] (StorePre 0x103063 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x180)) s (0x103063 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103063 0 (.sib 4 none 0 (.d32 0x180)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103063 0 (.sib 4 none 0 (.d32 0x180))).toInstrSpec (mov_m64_r64_effect_step 0x103063 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x180)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10306b [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10306b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10306b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10306b 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10306b 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10306b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103070 [0x48, 0x89, 0x84, 0x24, 0x78, 0x01, 0x00, 0x00] (StorePre 0x103070 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x103070 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103070 0 (.sib 4 none 0 (.d32 0x178)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103070 0 (.sib 4 none 0 (.d32 0x178))).toInstrSpec (mov_m64_r64_effect_step 0x103070 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x178)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x103078 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x103078 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103078 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103078 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103078 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103078 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10307d [0x48, 0x89, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00] (StorePre 0x10307d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x10307d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10307d 0 (.sib 4 none 0 (.d32 0x170)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10307d 0 (.sib 4 none 0 (.d32 0x170))).toInstrSpec (mov_m64_r64_effect_step 0x10307d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x170)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x103085 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x103085 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103085 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103085 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103085 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103085 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10308a [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x10308a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10308a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10308a 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10308a 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10308a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10308f [0x48, 0x89, 0x8C, 0x24, 0x68, 0x01, 0x00, 0x00] (StorePre 0x10308f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x10308f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10308f 1 (.sib 4 none 0 (.d32 0x168)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10308f 1 (.sib 4 none 0 (.d32 0x168))).toInstrSpec (mov_m64_r64_effect_step 0x10308f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x168)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x103097 [0x48, 0x89, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00] (StorePre 0x103097 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x103097 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103097 0 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103097 0 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (mov_m64_r64_effect_step 0x103097 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10309f [0x48, 0xB8, 0xAB, 0xD9, 0x83, 0x1F, 0x19, 0xCD, 0xE0, 0x5B] (fun s => s.RIP = 0x10309f) (movR64Imm64Effect 0x10309f 0 0x5be0cd191f83d9ab)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x10309f 0 0x5be0cd191f83d9ab).toInstrSpec (mov_r64_imm64_effect_step 0x10309f 0x48 0xb8 (by decide) (by decide) 0x5be0cd191f83d9ab) pre_rip
  have f17 : InstrSpec 0x1030a9 [0x48, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00] (StorePre 0x1030a9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1030a9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1030a9 0 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1030a9 0 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (mov_m64_r64_effect_step 0x1030a9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1030b1 [0x48, 0xB8, 0x7F, 0x52, 0x0E, 0x51, 0x8C, 0x68, 0x05, 0x9B] (fun s => s.RIP = 0x1030b1) (movR64Imm64Effect 0x1030b1 0 0x9b05688c510e527f)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1030b1 0 0x9b05688c510e527f).toInstrSpec (mov_r64_imm64_effect_step 0x1030b1 0x48 0xb8 (by decide) (by decide) 0x9b05688c510e527f) pre_rip
  have f19 : InstrSpec 0x1030bb [0x48, 0x89, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00] (StorePre 0x1030bb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1030bb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1030bb 0 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1030bb 0 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_m64_r64_effect_step 0x1030bb 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10303c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103044) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103049) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103051) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103056) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10305e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103063) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10306b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103070) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103078) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10307d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103085) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10308a) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10308f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103097) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10309f) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030a9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030b1) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 80), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030bb) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 80), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1030c3) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l103037_1 code

theorem block_l103037 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103037 :=
  Rest.liftedBlock (rest_l103037 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103037 x hx)

theorem rest_l103101 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103101 bytes_l103101) (entryMap (live .l103101))
      4 0x103101 bytes_l103101 b_l103101 := by
  have f0 : InstrSpec 0x103101 [0x48, 0x8D, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103101) (leaR64Effect 0x103101 7 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103101 7 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x103101 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103109 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x103109) (movR64R64Effect 0x103109 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103109 6 14).toInstrSpec (mov_r64_r64_effect_step 0x103109 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10310c [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x10310c) (movR64R64Effect 0x10310c 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10310c 2 3).toInstrSpec (mov_r64_r64_effect_step 0x10310c 0x48 0xda (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10310f [0xFF, 0x15, 0xBB, 0x0C, 0x10, 0x00] (GoesTo (CallMemPre 0x10310f (.rip 0x100cbb)) (callEffect (callMemPtr 0x10310f (.rip 0x100cbb)) (0x10310f + BitVec.ofNat 64 (callMemLen (.rip 0x100cbb)))) 0x12a820) (callEffect (callMemPtr 0x10310f (.rip 0x100cbb)) (0x10310f + BitVec.ofNat 64 (callMemLen (.rip 0x100cbb))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10310f (.rip 0x100cbb)).toInstrSpec (call_m64_effect_step 0x10310f (.rip 0x100cbb) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103109) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10310c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10310f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l103101 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103101 :=
  Rest.liftedBlock (rest_l103101 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103101 x hx)

theorem rest_l103115 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103115 bytes_l103115) (entryMap (live .l103115))
      2 0x103115 bytes_l103115 b_l103115 := by
  have f0 : InstrSpec 0x103115 [0x88, 0x9C, 0x24, 0x37, 0x01, 0x00, 0x00] (StorePre 0x103115 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x137)) s (0x103115 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x103115 7 3 (.sib 4 none 0 (.d32 0x137)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x103115 7 3 (.sib 4 none 0 (.d32 0x137))).toInstrSpec (mov_m8_r8_effect_step 0x103115 3 (by decide) (.sib 4 none 0 (.d32 0x137)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10311c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel8_effect_step 0x10311c 0x52 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l103115 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103115 :=
  Rest.liftedBlock (rest_l103115 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103115 x hx)

theorem rest_l10311e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10311e bytes_l10311e) (entryMap (live .l10311e))
      11 0x10311e bytes_l10311e b_l10311e := by
  have f0 : InstrSpec 0x10311e [0x48, 0x8D, 0xBC, 0x24, 0x38, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10311e) (leaR64Effect 0x10311e 7 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10311e 7 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (lea_r64_effect_step 0x10311e 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103126 [0x49, 0xBF, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x103126) (movR64Imm64Effect 0x103126 15 0x7fffffffffffffc0)
      [] [] [.reg 15, .rip] :=
    (movR64Imm64Effect_footprint 0x103126 15 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x103126 0x49 0xbf (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f2 : InstrSpec 0x103130 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x103130) (andR64R64Effect 0x103130 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x103130 15 3).toInstrSpec (and_r64_r64_effect_step 0x103130 0x49 0xdf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103133 [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x103133) (movR32R32Effect 0x103133 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x103133 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x103133 0x41 0xdc (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x103136 [0x41, 0x83, 0xE4, 0x3F] (fun s => s.RIP = 0x103136) (andR32Imm8Effect 0x103136 4 12 0x3f)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x103136 4 12 0x3f).toInstrSpec (and_r32_imm8_rex_effect_step 0x103136 0x41 0xe4 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10313a [0x4D, 0x01, 0xF7] (fun s => s.RIP = 0x10313a) (addR64R64Effect 0x10313a 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10313a 15 14).toInstrSpec (add_r64_r64_effect_step 0x10313a 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10313d [0x48, 0xC1, 0xEB, 0x06] (fun s => s.RIP = 0x10313d) (shrR64Effect 0x10313d 4 3 6)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x10313d 4 3 6).toInstrSpec (shr_r64_imm8_effect_step 0x10313d 0x48 0xeb 0x6 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103141 [0x48, 0x89, 0x9C, 0x24, 0x58, 0x01, 0x00, 0x00] (StorePre 0x103141 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x103141 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103141 3 (.sib 4 none 0 (.d32 0x158)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103141 3 (.sib 4 none 0 (.d32 0x158))).toInstrSpec (mov_m64_r64_effect_step 0x103141 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x158)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103149 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x103149) (movR64R64Effect 0x103149 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103149 6 14).toInstrSpec (mov_r64_r64_effect_step 0x103149 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10314c [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x10314c) (movR64R64Effect 0x10314c 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10314c 2 3).toInstrSpec (mov_r64_r64_effect_step 0x10314c 0x48 0xda (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10314f [0xE8, 0x8C, 0xE7, 0x01, 0x00] (PushPre 0x10314f 5) (callEffect (fun _ => 0x1218e0) 0x103154)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10314f 0x1218e0 0x103154).toInstrSpec (call_rel32_effect_step 0x10314f 0x1e78c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103126) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103130) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103133) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103136) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10313a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10313d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (3, 65), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103141) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (3, 65), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103149) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (3, 65), (4, 4), (5, 5), (6, 68), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10314c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 65), (4, 4), (5, 5), (6, 68), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10314f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 70), (3, 65), (4, 72), (5, 5), (6, 68), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 74) (by decide) (by decide) rfl rfl

theorem block_l10311e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10311e :=
  Rest.liftedBlock (rest_l10311e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10311e x hx)

theorem rest_l103154 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103154 bytes_l103154) (entryMap (live .l103154))
      5 0x103154 bytes_l103154 b_l103154 := by
  have f0 : InstrSpec 0x103154 [0x44, 0x88, 0xA4, 0x24, 0x37, 0x01, 0x00, 0x00] (StorePre 0x103154 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x137)) s (0x103154 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x103154 8 12 (.sib 4 none 0 (.d32 0x137)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x103154 8 12 (.sib 4 none 0 (.d32 0x137))).toInstrSpec (mov_m8_r8_rex_effect_step 0x103154 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0x137)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10315c [0x48, 0x8D, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10315c) (leaR64Effect 0x10315c 7 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10315c 7 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x10315c 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103164 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x103164) (movR64R64Effect 0x103164 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x103164 6 15).toInstrSpec (mov_r64_r64_effect_step 0x103164 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103167 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x103167) (movR64R64Effect 0x103167 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x103167 2 12).toInstrSpec (mov_r64_r64_effect_step 0x103167 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10316a [0xFF, 0x15, 0x60, 0x0C, 0x10, 0x00] (GoesTo (CallMemPre 0x10316a (.rip 0x100c60)) (callEffect (callMemPtr 0x10316a (.rip 0x100c60)) (0x10316a + BitVec.ofNat 64 (callMemLen (.rip 0x100c60)))) 0x12a820) (callEffect (callMemPtr 0x10316a (.rip 0x100c60)) (0x10316a + BitVec.ofNat 64 (callMemLen (.rip 0x100c60))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10316a (.rip 0x100c60)).toInstrSpec (call_m64_effect_step 0x10316a (.rip 0x100c60) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10315c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103164) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103167) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 58), (3, 3), (4, 4), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10316a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 62) (by decide) (by decide) rfl rfl

theorem block_l103154 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103154 :=
  Rest.liftedBlock (rest_l103154 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103154 x hx)

theorem rest_l103170 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103170 bytes_l103170) (entryMap (live .l103170))
      19 0x103170 bytes_l103170 b_l103170 := by
  have f0 : InstrSpec 0x103170 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x103170) (leaR64Effect 0x103170 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103170 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103170 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103175 [0x48, 0x8D, 0xB4, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103175) (leaR64Effect 0x103175 6 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103175 6 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x103175 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10317d [0xB9, 0x0D, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10317d) (movR32Imm32Effect 0x10317d 5 1 0xd)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10317d 5 1 0xd).toInstrSpec (mov_r32_imm32_effect_step 0x10317d 0xb9 (by decide) 0xd) pre_rip
  have f3 : InstrSpec 0x103182 [0xF3, 0x48, 0xA5] (RepPre 0x103182 (RepMovsqPre 0x103182)) (repMovsqEffect 0x103182)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x103182).toInstrSpecOfRuns (rep_movsq_runs hstride 0x103182 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f4 : InstrSpec 0x103185 [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x47] (LoadPre 0x103185 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x103185 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x103185 6 15 (.sib 4 none 0 (.d8 0x47)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x103185 6 15 (.sib 4 none 0 (.d8 0x47))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x103185 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10318b [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x10318b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10318b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10318b 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10318b 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10318b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x103190 [0x48, 0xC1, 0xE0, 0x09] (fun s => s.RIP = 0x103190) (shlR64Effect 0x103190 4 0 9)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR64Effect_footprint 0x103190 4 0 9).toInstrSpec (shl_r64_imm8_effect_step 0x103190 0x48 0xe0 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x103194 [0x4D, 0x89, 0xFE] (fun s => s.RIP = 0x103194) (movR64R64Effect 0x103194 14 15)
      [.gpr 15] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x103194 14 15).toInstrSpec (mov_r64_r64_effect_step 0x103194 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x103197 [0x42, 0xC6, 0x44, 0x3C, 0x08, 0x80] (StorePre 0x103197 6 (fun s => AddrMode.addr (.sib 4 (some 15) 0 (.d8 0x8)) s (0x103197 + BitVec.ofNat 64 6)) 1) (movM8Imm8RexEffect 0x103197 (.sib 4 (some 15) 0 (.d8 0x8)) 0x80)
      [.gpr 4, .gpr 15] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x103197 (.sib 4 (some 15) 0 (.d8 0x8)) 0x80).toInstrSpec (mov_m8_imm8_rex_effect_step 0x103197 0x42 (by decide) (.sib 4 (some 15) 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10319d [0x4A, 0x8D, 0x3C, 0x3C] (fun s => s.RIP = 0x10319d) (leaR64Effect 0x10319d 7 (.sib 4 (some 15) 0 .none))
      [.gpr 4, .gpr 15] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10319d 7 (.sib 4 (some 15) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10319d 0x4a (by decide) 7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1031a1 [0x48, 0x83, 0xC7, 0x09] (fun s => s.RIP = 0x1031a1) (addR64Imm8Effect 0x1031a1 7 0x9)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1031a1 7 0x9).toInstrSpec (add_r64_imm8_effect_step 0x1031a1 0x48 0xc7 0x9 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1031a5 [0x41, 0xC1, 0xE7, 0x03] (fun s => s.RIP = 0x1031a5) (shlR32Effect 0x1031a5 4 15 3)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR32Effect_footprint 0x1031a5 4 15 3).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1031a5 0x41 0xe7 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1031a9 [0x49, 0x09, 0xC7] (fun s => s.RIP = 0x1031a9) (orR64R64Effect 0x1031a9 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1031a9 15 0).toInstrSpec (or_r64_r64_effect_step 0x1031a9 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1031ac [0x48, 0x8D, 0x5C, 0x24, 0x48] (fun s => s.RIP = 0x1031ac) (leaR64Effect 0x1031ac 3 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x1031ac 3 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x1031ac 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1031b1 [0x49, 0x0F, 0xCF] (fun s => s.RIP = 0x1031b1) (bswapR64Effect 0x1031b1 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (bswapR64Effect_footprint 0x1031b1 3 15).toInstrSpec (bswap_r64_effect_step 0x1031b1 0x49 (by decide) 0xcf (by decide)) pre_rip
  have f15 : InstrSpec 0x1031b4 [0x49, 0x83, 0xF6, 0x3F] (fun s => s.RIP = 0x1031b4) (xorR64Imm8Effect 0x1031b4 14 0x3f)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x1031b4 14 0x3f).toInstrSpec (xor_r64_imm8_effect_step 0x1031b4 0x49 0xf6 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1031b8 [0x31, 0xF6] (fun s => s.RIP = 0x1031b8) (xorR32R32Effect 0x1031b8 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1031b8 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1031b8 0xf6 (by decide)) pre_rip
  have f17 : InstrSpec 0x1031ba [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x1031ba) (movR64R64Effect 0x1031ba 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1031ba 2 14).toInstrSpec (mov_r64_r64_effect_step 0x1031ba 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1031bd [0xFF, 0x15, 0x4D, 0x0C, 0x10, 0x00] (GoesTo (CallMemPre 0x1031bd (.rip 0x100c4d)) (callEffect (callMemPtr 0x1031bd (.rip 0x100c4d)) (0x1031bd + BitVec.ofNat 64 (callMemLen (.rip 0x100c4d)))) 0x12a700) (callEffect (callMemPtr 0x1031bd (.rip 0x100c4d)) (0x1031bd + BitVec.ofNat 64 (callMemLen (.rip 0x100c4d))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1031bd (.rip 0x100c4d)).toInstrSpec (call_m64_effect_step 0x1031bd (.rip 0x100c4d) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103175) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10317d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103182) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103185) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10318b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103190) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103194) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103197) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10319d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 70), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031a1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031a5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031a9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 65), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031ac) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 76), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031b1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031b4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 59), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031b8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 65), (3, 78), (4, 4), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031ba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 65), (2, 86), (3, 78), (4, 4), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031bd) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 65), (2, 86), (3, 78), (4, 88), (5, 5), (6, 84), (7, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 82), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f18 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 90) (by decide) (by decide) rfl rfl

theorem block_l103170 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103170 :=
  Rest.liftedBlock (rest_l103170 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103170 x hx)

theorem rest_l1031c3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1031c3 bytes_l1031c3) (entryMap (live .l1031c3))
      2 0x1031c3 bytes_l1031c3 b_l1031c3 := by
  have f0 : InstrSpec 0x1031c3 [0x49, 0x83, 0xFE, 0x07] (fun s => s.RIP = 0x1031c3) (cmpR64Imm8Effect 0x1031c3 14 0x7)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x1031c3 14 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x1031c3 0x49 0xfe 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031c7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x1031c7 7 0xbc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1031c3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1031c3 :=
  Rest.liftedBlock (rest_l1031c3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1031c3 x hx)

theorem rest_l1031cd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1031cd bytes_l1031cd) (entryMap (live .l1031cd))
      20 0x1031cd bytes_l1031cd b_l1031cd := by
  have f0 : InstrSpec 0x1031cd [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x1031cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1031cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1031cd 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1031cd 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1031cd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1031d2 [0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x1031d2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1031d2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1031d2 0 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1031d2 0 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x1031d2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1031da [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x1031da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1031da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1031da 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1031da 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1031da 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1031df [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x1031df 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1031df + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1031df 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1031df 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x1031df 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1031e7 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x1031e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1031e7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1031e7 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1031e7 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1031e7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1031ec [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x1031ec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1031ec + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1031ec 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1031ec 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1031ec 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1031f4 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1031f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1031f4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1031f4 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1031f4 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1031f4 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1031f9 [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x1031f9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1031f9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1031f9 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1031f9 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x1031f9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x103201 [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x103201 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103201 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103201 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103201 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x103201 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103206 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x103206 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x103206 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103206 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103206 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x103206 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10320e [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10320e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10320e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10320e 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10320e 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10320e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x103213 [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x103213 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x103213 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103213 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103213 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x103213 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10321b [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x10321b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10321b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10321b 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10321b 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10321b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x103220 [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x103220 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103220 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103220 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x103220 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x103220 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x103225 [0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x103225 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x103225 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x103225 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103225 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x103225 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10322d [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x10322d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10322d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10322d 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10322d 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x10322d 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x103235 [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103235) (leaR64Effect 0x103235 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x103235 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x103235 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10323d [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10323d) (movR32Imm32Effect 0x10323d 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10323d 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x10323d 0xba (by decide) 0x1) pre_rip
  have f18 : InstrSpec 0x103242 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x103242) (movR64R64Effect 0x103242 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103242 7 3).toInstrSpec (mov_r64_r64_effect_step 0x103242 0x48 0xdf (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x103245 [0xE8, 0x96, 0xE6, 0x01, 0x00] (PushPre 0x103245 5) (callEffect (fun _ => 0x1218e0) 0x10324a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103245 0x1218e0 0x10324a).toInstrSpec (call_rel32_effect_step 0x103245 0x1e696 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031da) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031df) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031e7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031ec) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031f4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1031f9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103201) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103206) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10320e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103213) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10321b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103220) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103225) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10322d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103235) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 73), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10323d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103242) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 4), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103245) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 71), (1, 73), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 81), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 85) (by decide) (by decide) rfl rfl

theorem block_l1031cd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1031cd :=
  Rest.liftedBlock (rest_l1031cd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1031cd x hx)

theorem rest_l10324a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10324a bytes_l10324a) (entryMap (live .l10324a))
      7 0x10324a bytes_l10324a b_l10324a := by
  have f0 : InstrSpec 0x10324a [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10324a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10324a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10324a (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10324a (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10324a 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103253 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103253 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x103253 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103253 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103253 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103253 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10325c [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10325c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10325c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10325c (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10325c (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10325c 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x103265 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103265 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103265 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103265 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103265 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103265 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10326e [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10326e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10326e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10326e (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10326e (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10326e 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x103277 [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103277 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x103277 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103277 (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103277 (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103277 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x103280 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103280 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103280 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x103280 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103280 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103280 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103253) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10325c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103265) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10326e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103277) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103280) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103289) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l10324a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10324a :=
  Rest.liftedBlock (rest_l10324a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10324a x hx)

theorem rest_l103289 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103289 bytes_l103289) (entryMap (live .l103289))
      20 0x103289 bytes_l103289 b_l103289 := by
  have f0 : InstrSpec 0x103289 [0x4C, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x103289 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103289 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103289 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x103289 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x103289 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10328e [0x4C, 0x89, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00] (StorePre 0x10328e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10328e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10328e 15 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10328e 15 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_m64_r64_effect_step 0x10328e 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103296 [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x103296 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x103296 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103296 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x103296 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x103296 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10329b [0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x10329b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10329b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10329b 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10329b 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x10329b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1032a3 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x1032a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1032a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032a3 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032a3 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1032a3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1032a8 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x1032a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1032a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032a8 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032a8 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1032a8 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1032b0 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x1032b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1032b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032b0 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032b0 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1032b0 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1032b5 [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x1032b5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1032b5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032b5 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032b5 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x1032b5 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1032bd [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x1032bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1032bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032bd 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032bd 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1032bd 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1032c2 [0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x1032c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1032c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032c2 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032c2 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x1032c2 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1032ca [0x48, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1032ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1032ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032ca 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032ca 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1032ca 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1032cf [0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x1032cf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1032cf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032cf 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032cf 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x1032cf 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1032d7 [0x48, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1032d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1032d7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032d7 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1032d7 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1032d7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1032dc [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x1032dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1032dc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1032dc 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1032dc 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1032dc 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1032e1 [0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x1032e1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1032e1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032e1 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032e1 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x1032e1 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1032e9 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x1032e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1032e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1032e9 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1032e9 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1032e9 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1032f1 [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1032f1) (leaR64Effect 0x1032f1 6 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1032f1 6 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x1032f1 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1032f9 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1032f9) (movR32Imm32Effect 0x1032f9 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1032f9 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1032f9 0xba (by decide) 0x1) pre_rip
  have f18 : InstrSpec 0x1032fe [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1032fe) (movR64R64Effect 0x1032fe 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1032fe 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1032fe 0x48 0xdf (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x103301 [0xE8, 0xDA, 0xE5, 0x01, 0x00] (PushPre 0x103301 5) (callEffect (fun _ => 0x1218e0) 0x103306)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103301 0x1218e0 0x103306).toInstrSpec (call_rel32_effect_step 0x103301 0x1e5da (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10328e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103296) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10329b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032a3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032a8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032b0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032b5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032bd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032c2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032ca) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032cf) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032d7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032dc) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032e1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032e9) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032f1) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 70), (1, 72), (3, 3), (4, 4), (5, 5), (6, 76), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032f9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 4), (5, 5), (6, 76), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1032fe) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 4), (5, 5), (6, 76), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103301) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 70), (1, 72), (2, 78), (3, 3), (4, 82), (5, 5), (6, 76), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1218e0) f19 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l103289 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103289 :=
  Rest.liftedBlock (rest_l103289 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103289 x hx)

theorem rest_l103306_1 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x103306 bytes_l103306) [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x103358 bytes_l103306_1 b_l103306_1 := by
  have f20 : InstrSpec 0x103358 [0x89, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x103358 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x103358 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x103358 7 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x103358 7 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m32_r32_low_effect_step 0x103358 7 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10335f [0x44, 0x89, 0x84, 0x24, 0x94, 0x00, 0x00, 0x00] (StorePre 0x10335f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x10335f + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x10335f 8 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10335f 8 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (mov_m32_r32_effect_step 0x10335f 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x103367 [0x44, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x103367 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x103367 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x103367 9 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x103367 9 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m32_r32_effect_step 0x103367 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x10336f [0x44, 0x89, 0x94, 0x24, 0x9C, 0x00, 0x00, 0x00] (StorePre 0x10336f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x10336f + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x10336f 10 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10336f 10 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (mov_m32_r32_effect_step 0x10336f 0x44 (by decide) 2 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x103377 [0x48, 0x8D, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103377) (leaR64Effect 0x103377 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103377 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x103377 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10337f [0x48, 0x8D, 0xB4, 0x24, 0xA0, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10337f) (leaR64Effect 0x10337f 6 (.sib 4 none 0 (.d32 0x1a0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10337f 6 (.sib 4 none 0 (.d32 0x1a0))).toInstrSpec (lea_r64_effect_step 0x10337f 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x1a0)) (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x103387 [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103387) (movR32Imm32Effect 0x103387 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x103387 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x103387 0xb9 (by decide) 0xb) pre_rip
  have f27 : InstrSpec 0x10338c [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10338c) (movR64R64Effect 0x10338c 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10338c 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10338c 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10338f [0xF3, 0x48, 0xA5] (RepPre 0x10338f (RepMovsqPre 0x10338f)) (repMovsqEffect 0x10338f)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10338f).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10338f 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f29 : InstrSpec 0x103392 [0x48, 0x8D, 0x5C, 0x24, 0x08] (fun s => s.RIP = 0x103392) (leaR64Effect 0x103392 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x103392 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103392 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x103397 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x103397) (movR64R64Effect 0x103397 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103397 7 3).toInstrSpec (mov_r64_r64_effect_step 0x103397 0x48 0xdf (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10339a [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10339a) (movR64R64Effect 0x10339a 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10339a 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10339a 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10339d [0xE8, 0x6E, 0xC6, 0x00, 0x00] (PushPre 0x10339d 5) (callEffect (fun _ => 0x10fa10) 0x1033a2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10339d 0x10fa10 0x1033a2).toInstrSpec (call_rel32_effect_step 0x10339d 0xc66e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10335f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103367) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10336f) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103377) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10337f) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 59), (2, 63), (4, 4), (5, 5), (6, 95), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103387) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 93), (1, 97), (2, 63), (4, 4), (5, 5), (6, 95), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10338c) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f27 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 93), (1, 97), (2, 63), (4, 4), (5, 5), (6, 95), (7, 99), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10338f) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 93), (1, 101), (2, 63), (4, 4), (5, 5), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103392) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f29 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 93), (1, 101), (2, 63), (3, 103), (4, 4), (5, 5), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103397) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f30 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 93), (1, 101), (2, 63), (3, 103), (4, 4), (5, 5), (7, 105), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10339a) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 93), (1, 101), (2, 63), (3, 103), (4, 4), (5, 5), (6, 107), (7, 105), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10339d) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f32 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 93), (1, 101), (2, 63), (3, 103), (4, 109), (5, 5), (6, 107), (7, 105), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa10) f32 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 111) (by decide) (by decide) rfl rfl

theorem rest_l103306 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103306 bytes_l103306) (entryMap (live .l103306))
      33 0x103306 bytes_l103306 b_l103306 := by
  have f0 : InstrSpec 0x103306 [0x8B, 0x44, 0x24, 0x48] (LoadPre 0x103306 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x103306 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103306 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x103306 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x103306 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10330a [0x8B, 0x4C, 0x24, 0x4C] (LoadPre 0x10330a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10330a + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10330a 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x10330a 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x10330a 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10330e [0x0F, 0xC8] (fun s => s.RIP = 0x10330e) (bswapR32Effect 0x10330e 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (bswapR32Effect_footprint 0x10330e 2 0).toInstrSpec (bswap_r32_effect_step 0x10330e 0xc8 (by decide)) pre_rip
  have f3 : InstrSpec 0x103310 [0x0F, 0xC9] (fun s => s.RIP = 0x103310) (bswapR32Effect 0x103310 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (bswapR32Effect_footprint 0x103310 2 1).toInstrSpec (bswap_r32_effect_step 0x103310 0xc9 (by decide)) pre_rip
  have f4 : InstrSpec 0x103312 [0x8B, 0x54, 0x24, 0x50] (LoadPre 0x103312 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x103312 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103312 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x103312 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r32_m32_low_effect_step 0x103312 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x103316 [0x0F, 0xCA] (fun s => s.RIP = 0x103316) (bswapR32Effect 0x103316 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR32Effect_footprint 0x103316 2 2).toInstrSpec (bswap_r32_effect_step 0x103316 0xca (by decide)) pre_rip
  have f6 : InstrSpec 0x103318 [0x8B, 0x74, 0x24, 0x54] (LoadPre 0x103318 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x103318 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x103318 6 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x103318 6 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_r32_m32_low_effect_step 0x103318 6 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10331c [0x0F, 0xCE] (fun s => s.RIP = 0x10331c) (bswapR32Effect 0x10331c 2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR32Effect_footprint 0x10331c 2 6).toInstrSpec (bswap_r32_effect_step 0x10331c 0xce (by decide)) pre_rip
  have f8 : InstrSpec 0x10331e [0x8B, 0x7C, 0x24, 0x58] (LoadPre 0x10331e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10331e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10331e 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x10331e 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r32_m32_low_effect_step 0x10331e 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x103322 [0x0F, 0xCF] (fun s => s.RIP = 0x103322) (bswapR32Effect 0x103322 2 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (bswapR32Effect_footprint 0x103322 2 7).toInstrSpec (bswap_r32_effect_step 0x103322 0xcf (by decide)) pre_rip
  have f10 : InstrSpec 0x103324 [0x44, 0x8B, 0x44, 0x24, 0x5C] (LoadPre 0x103324 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x103324 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x103324 8 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x103324 8 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_r32_m32_effect_step 0x103324 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x103329 [0x41, 0x0F, 0xC8] (fun s => s.RIP = 0x103329) (bswapR32Effect 0x103329 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (bswapR32Effect_footprint 0x103329 3 8).toInstrSpec (bswap_r32_rex_effect_step 0x103329 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f12 : InstrSpec 0x10332c [0x44, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x10332c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10332c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x10332c 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x10332c 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r32_m32_effect_step 0x10332c 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x103331 [0x41, 0x0F, 0xC9] (fun s => s.RIP = 0x103331) (bswapR32Effect 0x103331 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (bswapR32Effect_footprint 0x103331 3 9).toInstrSpec (bswap_r32_rex_effect_step 0x103331 0x41 (by decide) 0xc9 (by decide)) pre_rip
  have f14 : InstrSpec 0x103334 [0x44, 0x8B, 0x54, 0x24, 0x64] (LoadPre 0x103334 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x103334 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x103334 10 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x103334 10 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_r32_m32_effect_step 0x103334 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x103339 [0x41, 0x0F, 0xCA] (fun s => s.RIP = 0x103339) (bswapR32Effect 0x103339 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (bswapR32Effect_footprint 0x103339 3 10).toInstrSpec (bswap_r32_rex_effect_step 0x103339 0x41 (by decide) 0xca (by decide)) pre_rip
  have f16 : InstrSpec 0x10333c [0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10333c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10333c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10333c 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10333c 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m32_r32_low_effect_step 0x10333c 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x103343 [0x89, 0x8C, 0x24, 0x84, 0x00, 0x00, 0x00] (StorePre 0x103343 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x103343 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x103343 1 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x103343 1 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_m32_r32_low_effect_step 0x103343 1 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10334a [0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10334a 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10334a + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x10334a 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10334a 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m32_r32_low_effect_step 0x10334a 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x103351 [0x89, 0xB4, 0x24, 0x8C, 0x00, 0x00, 0x00] (StorePre 0x103351 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x103351 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x103351 6 (.sib 4 none 0 (.d32 0x8c)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x103351 6 (.sib 4 none 0 (.d32 0x8c))).toInstrSpec (mov_m32_r32_low_effect_step 0x103351 6 (.sib 4 none 0 (.d32 0x8c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10330a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10330e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103310) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103312) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 61), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103316) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103318) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 65), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10331c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10331e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 69), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103322) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103324) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 73), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103329) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10332c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103331) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103334) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 81), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103339) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10333c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103343) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10334a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103351) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 57), (1, 59), (2, 63), (4, 4), (5, 5), (6, 67), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103358) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l103306_1 hstride code

theorem block_l103306 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103306 :=
  Rest.liftedBlock (rest_l103306 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103306 x hx)

theorem rest_l1033a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033a2 bytes_l1033a2) (entryMap (live .l1033a2))
      6 0x1033a2 bytes_l1033a2 b_l1033a2 := by
  have f0 : InstrSpec 0x1033a2 [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1033a2) (leaR64Effect 0x1033a2 7 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1033a2 7 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (lea_r64_effect_step 0x1033a2 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1033aa [0x48, 0x8D, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1033aa) (leaR64Effect 0x1033aa 2 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1033aa 2 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x1033aa 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1033b2 [0x4C, 0x8D, 0x84, 0x24, 0x60, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1033b2) (leaR64Effect 0x1033b2 8 (.sib 4 none 0 (.d32 0x160)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x1033b2 8 (.sib 4 none 0 (.d32 0x160))).toInstrSpec (lea_r64_effect_step 0x1033b2 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x160)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1033ba [0xB9, 0x20, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1033ba) (movR32Imm32Effect 0x1033ba 5 1 0x20)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1033ba 5 1 0x20).toInstrSpec (mov_r32_imm32_effect_step 0x1033ba 0xb9 (by decide) 0x20) pre_rip
  have f4 : InstrSpec 0x1033bf [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1033bf) (movR64R64Effect 0x1033bf 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1033bf 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1033bf 0x48 0xde (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1033c2 [0xE8, 0x59, 0x1B, 0x00, 0x00] (PushPre 0x1033c2 5) (callEffect (fun _ => 0x104f20) 0x1033c7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1033c2 0x104f20 0x1033c7).toInstrSpec (call_rel32_effect_step 0x1033c2 0x1b59 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033aa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033ba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033bf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 55), (3, 3), (4, 4), (5, 5), (6, 61), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033c2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 59), (2, 55), (3, 3), (4, 63), (5, 5), (6, 61), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f20) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l1033a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033a2 :=
  Rest.liftedBlock (rest_l1033a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033a2 x hx)

theorem rest_l1033c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033c7 bytes_l1033c7) (entryMap (live .l1033c7))
      3 0x1033c7 bytes_l1033c7 b_l1033c7 := by
  have f0 : InstrSpec 0x1033c7 [0x48, 0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1033c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1033c7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1033c7 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1033c7 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x1033c7 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1033cf [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x1033cf) (testR64R64Effect 0x1033cf 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1033cf 0 0).toInstrSpec (test_r64_r64_effect_step 0x1033cf 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033cf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033d2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1033d2 4 0x25) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1033c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033c7 :=
  Rest.liftedBlock (rest_l1033c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033c7 x hx)

theorem rest_l1033d4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033d4 bytes_l1033d4) (entryMap (live .l1033d4))
      3 0x1033d4 bytes_l1033d4 b_l1033d4 := by
  have f0 : InstrSpec 0x1033d4 [0x48, 0x8B, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x1033d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1033d4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1033d4 7 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1033d4 7 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x1033d4 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1033dc [0x48, 0x85, 0xFF] (fun s => s.RIP = 0x1033dc) (testR64R64Effect 0x1033dc 7 7)
      [.gpr 7, .gpr 7] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1033dc 7 7).toInstrSpec (test_r64_r64_effect_step 0x1033dc 0x48 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033dc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1033df 4 0x18) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1033d4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033d4 :=
  Rest.liftedBlock (rest_l1033d4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033d4 x hx)

theorem rest_l1033e1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033e1 bytes_l1033e1) (entryMap (live .l1033e1))
      4 0x1033e1 bytes_l1033e1 b_l1033e1 := by
  have f0 : InstrSpec 0x1033e1 [0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x1033e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1033e1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1033e1 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1033e1 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x1033e1 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1033e9 [0x48, 0x8B, 0x09] (LoadPre 0x1033e9 (fun s => AddrMode.addr (.base 1 .none) s (0x1033e9 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1033e9 1 (.base 1 .none))
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1033e9 1 (.base 1 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1033e9 0x48 (by decide) 1 (.base 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1033ec [0x48, 0x85, 0xC9] (fun s => s.RIP = 0x1033ec) (testR64R64Effect 0x1033ec 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1033ec 1 1).toInstrSpec (test_r64_r64_effect_step 0x1033ec 0x48 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033e9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033ec) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033ef) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x1033ef 4 0x8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1033e1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033e1 :=
  Rest.liftedBlock (rest_l1033e1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033e1 x hx)

theorem rest_l1033f1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033f1 bytes_l1033f1) (entryMap (live .l1033f1))
      1 0x1033f1 bytes_l1033f1 b_l1033f1 := by
  have f0 : InstrSpec 0x1033f1 [0x48, 0x89, 0xC3] (fun s => s.RIP = 0x1033f1) (movR64R64Effect 0x1033f1 3 0)
      [.gpr 0] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x1033f1 3 0).toInstrSpec (mov_r64_r64_effect_step 0x1033f1 0x48 0xc3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0)]) (p' := 0x1033f4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1033f1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033f1 :=
  Rest.liftedBlock (rest_l1033f1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033f1 x hx)

theorem rest_l1033f6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033f6 bytes_l1033f6) (entryMap (live .l1033f6))
      1 0x1033f6 bytes_l1033f6 b_l1033f6 := by
  have f0 : InstrSpec 0x1033f6 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1033f6) (movR64R64Effect 0x1033f6 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1033f6 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1033f6 0x48 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1033f9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1033f6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033f6 :=
  Rest.liftedBlock (rest_l1033f6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033f6 x hx)

theorem rest_l1033f9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1033f9 bytes_l1033f9) (entryMap (live .l1033f9))
      6 0x1033f9 bytes_l1033f9 b_l1033f9 := by
  have f0 : InstrSpec 0x1033f9 [0x48, 0x81, 0xC4, 0xF8, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1033f9) (addR64Imm32Effect 0x1033f9 4 0x1f8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1033f9 4 0x1f8).toInstrSpec (add_r64_imm32_effect_step 0x1033f9 0x48 0xc4 0x1f8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103400 [0x5B] (PopPre 0x103400) (popR64Effect 0x103400 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103400 1 3).toInstrSpec (pop_r64_effect_step 0x103400 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x103401 [0x41, 0x5C] (PopPre 0x103401) (popR64Effect 0x103401 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103401 2 12).toInstrSpec (pop_r64_rex_effect_step 0x103401 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103403 [0x41, 0x5E] (PopPre 0x103403) (popR64Effect 0x103403 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103403 2 14).toInstrSpec (pop_r64_rex_effect_step 0x103403 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x103405 [0x41, 0x5F] (PopPre 0x103405) (popR64Effect 0x103405 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103405 2 15).toInstrSpec (pop_r64_rex_effect_step 0x103405 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x103407 [0xC3] (RetPre 0x103407) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103407).toInstrSpec (ret_effect_step 0x103407) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103400) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103401) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103403) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103405) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103407) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l1033f9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1033f9 :=
  Rest.liftedBlock (rest_l1033f9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1033f9 x hx)

theorem rest_l103408 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103408 bytes_l103408) (entryMap (live .l103408))
      4 0x103408 bytes_l103408 b_l103408 := by
  have f0 : InstrSpec 0x103408 [0x48, 0xC7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x103408 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x103408 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103408 (.sib 4 none 0 (.d32 0x100)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103408 (.sib 4 none 0 (.d32 0x100)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x103408 0x48 (by decide) (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x103414 [0x48, 0xC7, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (StorePre 0x103414 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x103414 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x103414 (.sib 4 none 0 (.d32 0xf8)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x103414 (.sib 4 none 0 (.d32 0xf8)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x103414 0x48 (by decide) (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103420 [0x48, 0x8D, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103420) (leaR64Effect 0x103420 7 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103420 7 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (lea_r64_effect_step 0x103420 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103428 [0xE8, 0x13, 0xCE, 0xFF, 0xFF] (PushPre 0x103428 5) (callEffect (fun _ => 0x100240) 0x10342d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103428 0x100240 0x10342d).toInstrSpec (call_rel32_effect_step 0x103428 0xffffce13 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103414) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103420) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103428) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100240) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l103408 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103408 :=
  Rest.liftedBlock (rest_l103408 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103408 x hx)

theorem rest_l10342d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10342d bytes_l10342d) (entryMap (live .l10342d))
      1 0x10342d bytes_l10342d b_l10342d := by
  have f0 : InstrSpec 0x10342d [0xE8, 0xFE, 0xD5, 0xFF, 0xFF] (PushPre 0x10342d 5) (callEffect (fun _ => 0x100a30) 0x103432)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10342d 0x100a30 0x103432).toInstrSpec (call_rel32_effect_step 0x10342d 0xffffd5fe (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l10342d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10342d :=
  Rest.liftedBlock (rest_l10342d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10342d x hx)

theorem rest_l103432 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103432 bytes_l103432) (entryMap (live .l103432))
      2 0x103432 bytes_l103432 b_l103432 := by
  have f0 : InstrSpec 0x103432 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x103432) (leaR64Effect 0x103432 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x103432 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103432 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103437 [0xE8, 0x44, 0xCD, 0xFF, 0xFF] (PushPre 0x103437 5) (callEffect (fun _ => 0x100180) 0x10343c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103437 0x100180 0x10343c).toInstrSpec (call_rel32_effect_step 0x103437 0xffffcd44 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103437) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100180) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l103432 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103432 :=
  Rest.liftedBlock (rest_l103432 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103432 x hx)

theorem rest_l10343c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10343c bytes_l10343c) (entryMap (live .l10343c))
      1 0x10343c bytes_l10343c b_l10343c := by
  have f0 : InstrSpec 0x10343c [0xE8, 0xEF, 0xD5, 0xFF, 0xFF] (PushPre 0x10343c 5) (callEffect (fun _ => 0x100a30) 0x103441)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10343c 0x100a30 0x103441).toInstrSpec (call_rel32_effect_step 0x10343c 0xffffd5ef (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := []) (p' := 0x100a30) f0 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.call (n := 54) (by decide) (by decide) rfl rfl

theorem block_l10343c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10343c :=
  Rest.liftedBlock (rest_l10343c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10343c x hx)

theorem rest_l103441 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103441 bytes_l103441) (entryMap (live .l103441))
      2 0x103441 bytes_l103441 b_l103441 := by
  have f0 : InstrSpec 0x103441 [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x103441) (fun _ => nopEffect 0x103441 10)
      [] [] [.rip] :=
    (nopEffect_footprint 0x103441 10).toInstrSpec (nop_m_effect_step 0x103441 [0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10344b [0x0F, 0x1F, 0x44, 0x00, 0x00] (fun s => s.RIP = 0x10344b) (fun _ => nopEffect 0x10344b 5)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10344b 5).toInstrSpec (nop_m_effect_step 0x10344b [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10344b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103450) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l103441 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103441 :=
  Rest.liftedBlock (rest_l103441 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103441 x hx)

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

theorem_by block_l102fc0_eval :
    program.runBlock (dialect code) ⟨.l102fc0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102fe9_eval :
    program.runBlock (dialect code) ⟨.l102fe9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102ff4_eval :
    program.runBlock (dialect code) ⟨.l102ff4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10302c_eval :
    program.runBlock (dialect code) ⟨.l10302c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103037_eval :
    program.runBlock (dialect code) ⟨.l103037, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103101_eval :
    program.runBlock (dialect code) ⟨.l103101, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103115_eval :
    program.runBlock (dialect code) ⟨.l103115, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10311e_eval :
    program.runBlock (dialect code) ⟨.l10311e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103154_eval :
    program.runBlock (dialect code) ⟨.l103154, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103170_eval :
    program.runBlock (dialect code) ⟨.l103170, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1031c3_eval :
    program.runBlock (dialect code) ⟨.l1031c3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1031cd_eval :
    program.runBlock (dialect code) ⟨.l1031cd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10324a_eval :
    program.runBlock (dialect code) ⟨.l10324a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103289_eval :
    program.runBlock (dialect code) ⟨.l103289, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103306_eval :
    program.runBlock (dialect code) ⟨.l103306, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033a2_eval :
    program.runBlock (dialect code) ⟨.l1033a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033c7_eval :
    program.runBlock (dialect code) ⟨.l1033c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033d4_eval :
    program.runBlock (dialect code) ⟨.l1033d4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033e1_eval :
    program.runBlock (dialect code) ⟨.l1033e1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033f1_eval :
    program.runBlock (dialect code) ⟨.l1033f1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033f6_eval :
    program.runBlock (dialect code) ⟨.l1033f6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1033f9_eval :
    program.runBlock (dialect code) ⟨.l1033f9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103408_eval :
    program.runBlock (dialect code) ⟨.l103408, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10342d_eval :
    program.runBlock (dialect code) ⟨.l10342d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103432_eval :
    program.runBlock (dialect code) ⟨.l103432, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10343c_eval :
    program.runBlock (dialect code) ⟨.l10343c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103441_eval :
    program.runBlock (dialect code) ⟨.l103441, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
