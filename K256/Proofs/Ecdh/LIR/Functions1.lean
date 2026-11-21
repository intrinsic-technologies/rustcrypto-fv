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

theorem rest_l100a20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a20 bytes_l100a20) (entryMap (live .l100a20))
      1 0x100a20 bytes_l100a20 b_l100a20 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x100a20 0xfe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100a20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a20 :=
  Rest.liftedBlock (rest_l100a20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a20 x hx)

theorem rest_l100a30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a30 bytes_l100a30) (entryMap (live .l100a30))
      1 0x100a30 bytes_l100a30 b_l100a30 := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x100a30 0xfe (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100a30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a30 :=
  Rest.liftedBlock (rest_l100a30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a30 x hx)

theorem rest_l108890 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108890 bytes_l108890) (entryMap (live .l108890))
      8 0x108890 bytes_l108890 b_l108890 := by
  have f0 : InstrSpec 0x108890 [0x55] (PushPre 0x108890 1) (pushR64Effect 0x108890 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108890 1 5).toInstrSpec (push_r64_effect_step 0x108890 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x108891 [0x41, 0x56] (PushPre 0x108891 2) (pushR64Effect 0x108891 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108891 2 14).toInstrSpec (push_r64_rex_effect_step 0x108891 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x108893 [0x53] (PushPre 0x108893 1) (pushR64Effect 0x108893 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x108893 1 3).toInstrSpec (push_r64_effect_step 0x108893 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x108894 [0x48, 0x83, 0xEC, 0x30] (fun s => s.RIP = 0x108894) (subR64Imm8Effect 0x108894 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x108894 4 0x30).toInstrSpec (sub_r64_imm8_effect_step 0x108894 0x48 0xec 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x108898 [0x44, 0x89, 0xCD] (fun s => s.RIP = 0x108898) (movR32R32Effect 0x108898 3 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x108898 3 5 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x108898 0x44 0xcd (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10889b [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10889b) (movR64R64Effect 0x10889b 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10889b 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10889b 0x48 0xfb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10889e [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x10889e) (movR64R64Effect 0x10889e 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10889e 7 4).toInstrSpec (mov_r64_r64_effect_step 0x10889e 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1088a1 [0xE8, 0x3A, 0xFC, 0xFF, 0xFF] (PushPre 0x1088a1 5) (callEffect (fun _ => 0x1084e0) 0x1088a6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1088a1 0x1084e0 0x1088a6).toInstrSpec (call_rel32_effect_step 0x1088a1 0xfffffc3a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108891) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108893) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108894) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108898) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10889b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 63), (4, 59), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10889e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 63), (4, 59), (5, 61), (6, 6), (7, 65), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088a1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 63), (4, 67), (5, 61), (6, 6), (7, 65), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e0) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 69) (by decide) (by decide) rfl rfl

theorem block_l108890 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108890 :=
  Rest.liftedBlock (rest_l108890 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108890 x hx)

theorem rest_l1088a6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1088a6 bytes_l1088a6) (entryMap (live .l1088a6))
      4 0x1088a6 bytes_l1088a6 b_l1088a6 := by
  have f0 : InstrSpec 0x1088a6 [0xB8, 0x40, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1088a6) (movR32Imm32Effect 0x1088a6 5 0 0x40)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1088a6 5 0 0x40).toInstrSpec (mov_r32_imm32_effect_step 0x1088a6 0xb8 (by decide) 0x40) pre_rip
  have f1 : InstrSpec 0x1088ab [0x29, 0xE8] (fun s => s.RIP = 0x1088ab) (subR32R32Effect 0x1088ab 2 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (subR32R32Effect_footprint 0x1088ab 2 0 5).toInstrSpec (sub_r32_r32_effect_step 0x1088ab 0xe8 (by decide)) pre_rip
  have f2 : InstrSpec 0x1088ad [0x83, 0xF8, 0x40] (fun s => s.RIP = 0x1088ad) (cmpR32Imm8Effect 0x1088ad 3 0 0x40)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1088ad 3 0 0x40).toInstrSpec (cmp_r32_imm8_effect_step 0x1088ad 0xf8 0x40 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ab) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ad) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088b0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x1088b0 3 0x9c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1088a6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1088a6 :=
  Rest.liftedBlock (rest_l1088a6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1088a6 x hx)

theorem rest_l1088b6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1088b6 bytes_l1088b6) (entryMap (live .l1088b6))
      2 0x1088b6 bytes_l1088b6 b_l1088b6 := by
  have f0 : InstrSpec 0x1088b6 [0x83, 0xFD, 0x40] (fun s => s.RIP = 0x1088b6) (cmpR32Imm8Effect 0x1088b6 3 5 0x40)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1088b6 3 5 0x40).toInstrSpec (cmp_r32_imm8_effect_step 0x1088b6 0xfd 0x40 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1088b9 3 0x7f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1088b6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1088b6 :=
  Rest.liftedBlock (rest_l1088b6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1088b6 x hx)

theorem rest_l1088bb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1088bb bytes_l1088bb) (entryMap (live .l1088bb))
      2 0x1088bb bytes_l1088bb b_l1088bb := by
  have f0 : InstrSpec 0x1088bb [0x85, 0xED] (fun s => s.RIP = 0x1088bb) (testR32R32Effect 0x1088bb 2 5 5)
      [.gpr 5, .gpr 5] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x1088bb 2 5 5).toInstrSpec (test_r32_r32_effect_step 0x1088bb 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088bd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1088bd 4 0xa7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1088bb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1088bb :=
  Rest.liftedBlock (rest_l1088bb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1088bb x hx)

theorem rest_l1088c3_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x1088c3 bytes_l1088c3) [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 91), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      19 0x108906 bytes_l1088c3_1 b_l1088c3_1 := by
  have f20 : InstrSpec 0x108906 [0x89, 0xE9] (fun s => s.RIP = 0x108906) (movR32R32Effect 0x108906 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108906 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x108906 0xe9 (by decide)) pre_rip
  have f21 : InstrSpec 0x108908 [0x49, 0xD3, 0xEE] (fun s => s.RIP = 0x108908) (shrR64ClEffect 0x108908 3 14)
      [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x108908 3 14).toInstrSpec (shr_r64_cl_effect_step 0x108908 0x49 0xee (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10890b [0x89, 0xC1] (fun s => s.RIP = 0x10890b) (movR32R32Effect 0x10890b 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10890b 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10890b 0xc1 (by decide)) pre_rip
  have f23 : InstrSpec 0x10890d [0x48, 0xD3, 0xE6] (fun s => s.RIP = 0x10890d) (shlR64ClEffect 0x10890d 3 6)
      [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x10890d 3 6).toInstrSpec (shl_r64_cl_effect_step 0x10890d 0x48 0xe6 (by decide) (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x108910 [0x89, 0xE9] (fun s => s.RIP = 0x108910) (movR32R32Effect 0x108910 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x108910 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x108910 0xe9 (by decide)) pre_rip
  have f25 : InstrSpec 0x108912 [0x48, 0xD3, 0xEA] (fun s => s.RIP = 0x108912) (shrR64ClEffect 0x108912 3 2)
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x108912 3 2).toInstrSpec (shr_r64_cl_effect_step 0x108912 0x48 0xea (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x108915 [0x4D, 0x09, 0xC3] (fun s => s.RIP = 0x108915) (orR64R64Effect 0x108915 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108915 11 8).toInstrSpec (or_r64_r64_effect_step 0x108915 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x108918 [0x49, 0x09, 0xFE] (fun s => s.RIP = 0x108918) (orR64R64Effect 0x108918 14 7)
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (orR64R64Effect_footprint 0x108918 14 7).toInstrSpec (or_r64_r64_effect_step 0x108918 0x49 0xfe (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10891b [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x10891b) (orR64R64Effect 0x10891b 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10891b 2 6).toInstrSpec (or_r64_r64_effect_step 0x10891b 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10891e [0x48, 0x89, 0x13] (StorePre 0x10891e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10891e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10891e 2 (.base 3 .none))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10891e 2 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10891e 0x48 (by decide) 2 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x108921 [0x4C, 0x89, 0x73, 0x08] (StorePre 0x108921 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x108921 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108921 14 (.base 3 (.d8 0x8)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x108921 14 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x108921 0x4c (by decide) 6 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x108925 [0x4C, 0x89, 0x5B, 0x10] (StorePre 0x108925 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x108925 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108925 11 (.base 3 (.d8 0x10)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x108925 11 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x108925 0x4c (by decide) 3 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x108929 [0x4C, 0x89, 0x4B, 0x18] (StorePre 0x108929 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x108929 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108929 9 (.base 3 (.d8 0x18)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x108929 9 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x108929 0x4c (by decide) 1 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x10892d [0x44, 0x88, 0x53, 0x20] (StorePre 0x10892d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10892d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10892d 4 10 (.base 3 (.d8 0x20)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x10892d 4 10 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10892d 0x44 (by decide) 2 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x108931 [0x48, 0x83, 0xC4, 0x30] (fun s => s.RIP = 0x108931) (addR64Imm8Effect 0x108931 4 0x30)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x108931 4 0x30).toInstrSpec (add_r64_imm8_effect_step 0x108931 0x48 0xc4 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x108935 [0x5B] (PopPre 0x108935) (popR64Effect 0x108935 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108935 1 3).toInstrSpec (pop_r64_effect_step 0x108935 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f36 : InstrSpec 0x108936 [0x41, 0x5E] (PopPre 0x108936) (popR64Effect 0x108936 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108936 2 14).toInstrSpec (pop_r64_rex_effect_step 0x108936 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f37 : InstrSpec 0x108938 [0x5D] (PopPre 0x108938) (popR64Effect 0x108938 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x108938 1 5).toInstrSpec (pop_r64_effect_step 0x108938 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f38 : InstrSpec 0x108939 [0xC3] (RetPre 0x108939) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x108939).toInstrSpec (ret_effect_step 0x108939) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 93), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 91), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108908) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 93), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10890b) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 97), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10890d) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 97), (2, 53), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108910) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 0), (1, 101), (2, 53), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108912) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 0), (1, 101), (2, 103), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108915) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 101), (2, 103), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 95), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108918) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 0), (1, 101), (2, 103), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10891b) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10891e) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108921) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108925) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108929) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10892d) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.exec (n := 115) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 4), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108931) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f34 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 3), (4, 116), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108935) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 119) f35 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 119), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 107), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108936) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 122) f36 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 123) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 122), (5, 5), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108938) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 125) f37 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 126) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 125), (5, 124), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108939) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f38 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f38 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 129) (ρ' := [(0, 0), (1, 101), (2, 109), (3, 118), (4, 128), (5, 124), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f38 (by decide) rfl rfl rfl (by decide)

theorem rest_l1088c3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1088c3 bytes_l1088c3) (entryMap (live .l1088c3))
      39 0x1088c3 bytes_l1088c3 b_l1088c3 := by
  have f0 : InstrSpec 0x1088c3 [0x48, 0x8B, 0x14, 0x24] (LoadPre 0x1088c3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1088c3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1088c3 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1088c3 2 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1088c3 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1088c7 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x1088c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1088c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088c7 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1088c7 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1088c7 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1088cc [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x1088cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1088cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088cc 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1088cc 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1088cc 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1088d1 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x1088d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1088d1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088d1 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1088d1 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1088d1 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1088d6 [0x4C, 0x8B, 0x5C, 0x24, 0x20] (LoadPre 0x1088d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1088d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088d6 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1088d6 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1088d6 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1088db [0x89, 0xC1] (fun s => s.RIP = 0x1088db) (movR32R32Effect 0x1088db 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088db 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1088db 0xc1 (by decide)) pre_rip
  have f6 : InstrSpec 0x1088dd [0x49, 0xD3, 0xE3] (fun s => s.RIP = 0x1088dd) (shlR64ClEffect 0x1088dd 3 11)
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x1088dd 3 11).toInstrSpec (shl_r64_cl_effect_step 0x1088dd 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1088e0 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x1088e0) (movR64R64Effect 0x1088e0 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1088e0 9 8).toInstrSpec (mov_r64_r64_effect_step 0x1088e0 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1088e3 [0x89, 0xE9] (fun s => s.RIP = 0x1088e3) (movR32R32Effect 0x1088e3 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088e3 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x1088e3 0xe9 (by decide)) pre_rip
  have f9 : InstrSpec 0x1088e5 [0x49, 0xD3, 0xE9] (fun s => s.RIP = 0x1088e5) (shrR64ClEffect 0x1088e5 3 9)
      [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x1088e5 3 9).toInstrSpec (shr_r64_cl_effect_step 0x1088e5 0x49 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1088e8 [0x89, 0xC1] (fun s => s.RIP = 0x1088e8) (movR32R32Effect 0x1088e8 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088e8 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1088e8 0xc1 (by decide)) pre_rip
  have f11 : InstrSpec 0x1088ea [0x49, 0xD3, 0xE0] (fun s => s.RIP = 0x1088ea) (shlR64ClEffect 0x1088ea 3 8)
      [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x1088ea 3 8).toInstrSpec (shl_r64_cl_effect_step 0x1088ea 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1088ed [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x28] (LoadPre 0x1088ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1088ed + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1088ed 6 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x1088ed 6 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1088ed 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1088f3 [0x4D, 0x09, 0xD9] (fun s => s.RIP = 0x1088f3) (orR64R64Effect 0x1088f3 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x1088f3 9 11).toInstrSpec (or_r64_r64_effect_step 0x1088f3 0x4d 0xd9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1088f6 [0x49, 0x89, 0xFB] (fun s => s.RIP = 0x1088f6) (movR64R64Effect 0x1088f6 11 7)
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x1088f6 11 7).toInstrSpec (mov_r64_r64_effect_step 0x1088f6 0x49 0xfb (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1088f9 [0x89, 0xE9] (fun s => s.RIP = 0x1088f9) (movR32R32Effect 0x1088f9 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088f9 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x1088f9 0xe9 (by decide)) pre_rip
  have f16 : InstrSpec 0x1088fb [0x49, 0xD3, 0xEB] (fun s => s.RIP = 0x1088fb) (shrR64ClEffect 0x1088fb 3 11)
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x1088fb 3 11).toInstrSpec (shr_r64_cl_effect_step 0x1088fb 0x49 0xeb (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1088fe [0x89, 0xC1] (fun s => s.RIP = 0x1088fe) (movR32R32Effect 0x1088fe 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1088fe 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1088fe 0xc1 (by decide)) pre_rip
  have f18 : InstrSpec 0x108900 [0x48, 0xD3, 0xE7] (fun s => s.RIP = 0x108900) (shlR64ClEffect 0x108900 3 7)
      [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x108900 3 7).toInstrSpec (shl_r64_cl_effect_step 0x108900 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x108903 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x108903) (movR64R64Effect 0x108903 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x108903 14 6).toInstrSpec (mov_r64_r64_effect_step 0x108903 0x49 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088c7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088cc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088d1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088d6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (11, 61), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088db) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (11, 61), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088dd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 67), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 67), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 71), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088e8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 71), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ea) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 71), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088ed) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 71), (10, 77), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088f3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088f6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 81), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088f9) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 83), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 81), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088fb) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 83), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1088fe) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108900) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108903) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 91), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x108906) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1088c3_1 code

theorem block_l1088c3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1088c3 :=
  Rest.liftedBlock (rest_l1088c3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1088c3 x hx)

theorem rest_l10893a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10893a bytes_l10893a) (entryMap (live .l10893a))
      4 0x10893a bytes_l10893a b_l10893a := by
  have f0 : InstrSpec 0x10893a [0xBE, 0x1B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10893a) (movR32Imm32Effect 0x10893a 5 6 0x1b)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10893a 5 6 0x1b).toInstrSpec (mov_r32_imm32_effect_step 0x10893a 0xbe (by decide) 0x1b) pre_rip
  have f1 : InstrSpec 0x10893f [0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x10893f) (movR64Imm32Effect 0x10893f 7 0x202b38)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x10893f 7 0x202b38).toInstrSpec (mov_r64_imm32_effect_step 0x10893f 0x48 0xc7 (by decide) (by decide) (by decide) 0x202b38) pre_rip
  have f2 : InstrSpec 0x108946 [0x48, 0xC7, 0xC2, 0x58, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x108946) (movR64Imm32Effect 0x108946 2 0x202b58)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x108946 2 0x202b58).toInstrSpec (mov_r64_imm32_effect_step 0x108946 0x48 0xc2 (by decide) (by decide) (by decide) 0x202b58) pre_rip
  have f3 : InstrSpec 0x10894d [0xE8, 0x0E, 0x0C, 0x02, 0x00] (PushPre 0x10894d 5) (callEffect (fun _ => 0x129560) 0x108952)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10894d 0x129560 0x108952).toInstrSpec (call_rel32_effect_step 0x10894d 0x20c0e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x10893f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x108946) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x10894d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129560) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10893a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10893a :=
  Rest.liftedBlock (rest_l10893a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10893a x hx)

theorem rest_l108952 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x108952 bytes_l108952) (entryMap (live .l108952))
      4 0x108952 bytes_l108952 b_l108952 := by
  have f0 : InstrSpec 0x108952 [0xBE, 0x1B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x108952) (movR32Imm32Effect 0x108952 5 6 0x1b)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x108952 5 6 0x1b).toInstrSpec (mov_r32_imm32_effect_step 0x108952 0xbe (by decide) 0x1b) pre_rip
  have f1 : InstrSpec 0x108957 [0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x108957) (movR64Imm32Effect 0x108957 7 0x202b38)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x108957 7 0x202b38).toInstrSpec (mov_r64_imm32_effect_step 0x108957 0x48 0xc7 (by decide) (by decide) (by decide) 0x202b38) pre_rip
  have f2 : InstrSpec 0x10895e [0x48, 0xC7, 0xC2, 0x08, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x10895e) (movR64Imm32Effect 0x10895e 2 0x202b08)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x10895e 2 0x202b08).toInstrSpec (mov_r64_imm32_effect_step 0x10895e 0x48 0xc2 (by decide) (by decide) (by decide) 0x202b08) pre_rip
  have f3 : InstrSpec 0x108965 [0xE8, 0xF6, 0x0B, 0x02, 0x00] (PushPre 0x108965 5) (callEffect (fun _ => 0x129560) 0x10896a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x108965 0x129560 0x10896a).toInstrSpec (call_rel32_effect_step 0x108965 0x20bf6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 53)]) (p' := 0x108957) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x10895e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 53), (7, 55)]) (p' := 0x108965) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)]) (p' := 0x129560) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l108952 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l108952 :=
  Rest.liftedBlock (rest_l108952 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l108952 x hx)

theorem rest_l10896a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10896a bytes_l10896a) (entryMap (live .l10896a))
      4 0x10896a bytes_l10896a b_l10896a := by
  have f0 : InstrSpec 0x10896a [0xBF, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10896a) (movR32Imm32Effect 0x10896a 5 7 0x4)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10896a 5 7 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10896a 0xbf (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x10896f [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10896f) (movR32Imm32Effect 0x10896f 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10896f 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10896f 0xbe (by decide) 0x4) pre_rip
  have f2 : InstrSpec 0x108974 [0x48, 0xC7, 0xC2, 0x20, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x108974) (movR64Imm32Effect 0x108974 2 0x202b20)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x108974 2 0x202b20).toInstrSpec (mov_r64_imm32_effect_step 0x108974 0x48 0xc2 (by decide) (by decide) (by decide) 0x202b20) pre_rip
  have f3 : InstrSpec 0x10897b [0xE8, 0x72, 0x0C, 0x02, 0x00] (PushPre 0x10897b 5) (callEffect (fun _ => 0x1295f2) 0x108980)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10897b 0x1295f2 0x108980).toInstrSpec (call_rel32_effect_step 0x10897b 0x20c72 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (7, 53)]) (p' := 0x10896f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x108974) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (5, 5), (6, 55), (7, 53)]) (p' := 0x10897b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)]) (p' := 0x1295f2) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10896a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10896a :=
  Rest.liftedBlock (rest_l10896a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10896a x hx)

theorem rest_l109e60_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x109e60 bytes_l109e60) [(1, 97), (2, 124), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x109eef bytes_l109e60_2 b_l109e60_2 := by
  have f40 : InstrSpec 0x109eef [0x4C, 0x01, 0xFA] (fun s => s.RIP = 0x109eef) (addR64R64Effect 0x109eef 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109eef 2 15).toInstrSpec (add_r64_r64_effect_step 0x109eef 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x109ef2 [0x48, 0x83, 0xC2, 0x02] (fun s => s.RIP = 0x109ef2) (addR64Imm8Effect 0x109ef2 2 0x2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109ef2 2 0x2).toInstrSpec (add_r64_imm8_effect_step 0x109ef2 0x48 0xc2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x109ef6 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x109ef6) (orR64R64Effect 0x109ef6 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109ef6 2 6).toInstrSpec (or_r64_r64_effect_step 0x109ef6 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x109ef9 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x109ef9) (shrR64Effect 0x109ef9 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x109ef9 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x109ef9 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x109efd [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x109efd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109efd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109efd 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109efd 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109efd 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x109f02 [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x109f02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f02 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109f02 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109f02 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109f02 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x109f07 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x109f07) (sarR64Effect 0x109f07 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x109f07 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x109f07 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x109f0b [0x4C, 0x01, 0xF1] (fun s => s.RIP = 0x109f0b) (addR64R64Effect 0x109f0b 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109f0b 1 14).toInstrSpec (add_r64_r64_effect_step 0x109f0b 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x109f0e [0x48, 0xFF, 0xC1] (fun s => s.RIP = 0x109f0e) (incR64Effect 0x109f0e 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (incR64Effect_footprint 0x109f0e 1).toInstrSpec (inc_r64_effect_step 0x109f0e 0x48 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x109f11 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x109f11) (movR64R64Effect 0x109f11 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x109f11 2 14).toInstrSpec (mov_r64_r64_effect_step 0x109f11 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x109f14 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x109f14) (notR64Effect 0x109f14 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x109f14 2).toInstrSpec (not_r64_effect_step 0x109f14 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x109f17 [0x48, 0x09, 0xCA] (fun s => s.RIP = 0x109f17) (orR64R64Effect 0x109f17 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109f17 2 1).toInstrSpec (or_r64_r64_effect_step 0x109f17 0x48 0xca (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x109f1a [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x109f1a) (shrR64Effect 0x109f1a 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x109f1a 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x109f1a 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x109f1e [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x109f1e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f1e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109f1e 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f1e 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109f1e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x109f23 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x109f23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f23 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109f23 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109f23 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x109f23 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x109f28 [0x24, 0x01] (fun s => s.RIP = 0x109f28) (andAlImm8Effect 0x109f28 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x109f28 0x1).toInstrSpec (and_al_imm8_effect_step 0x109f28 0x1) pre_rip
  have f56 : InstrSpec 0x109f2a [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x109f2a) (movzxR32R8Effect 0x109f2a 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x109f2a 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x109f2a 0xf8 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x109f2d [0xE8, 0x1E, 0xDE, 0x01, 0x00] (PushPre 0x109f2d 5) (callEffect (fun _ => 0x127d50) 0x109f32)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109f2d 0x127d50 0x109f32).toInstrSpec (call_rel32_effect_step 0x109f2d 0x1de1e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(1, 97), (2, 130), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef2) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(1, 97), (2, 132), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef6) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(1, 97), (2, 134), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ef9) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(1, 97), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109efd) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(1, 97), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f02) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(1, 139), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f07) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(1, 141), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f0b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f47 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(1, 143), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f0e) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f48 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(1, 145), (2, 136), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f11) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f49 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(1, 145), (2, 147), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f14) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(1, 145), (2, 149), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f17) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f51 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(1, 145), (2, 151), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f1a) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f1e) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.exec (n := 155) (ρ' := [(1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f23) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f54 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 156), (1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f28) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f55 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 158), (1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f2a) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f56 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 158), (1, 145), (2, 153), (3, 65), (4, 63), (5, 5), (6, 128), (7, 160), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f2d) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f57 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 158), (1, 145), (2, 153), (3, 65), (4, 162), (5, 5), (6, 128), (7, 160), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f57 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 164) (by decide) (by decide) rfl rfl

theorem rest_l109e60_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x109e60 bytes_l109e60) [(0, 85), (1, 91), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      38 0x109ea1 bytes_l109e60_1 b_l109e60_1 := by
  have f20 : InstrSpec 0x109ea1 [0x48, 0xC1, 0xE9, 0x3F] (fun s => s.RIP = 0x109ea1) (shrR64Effect 0x109ea1 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x109ea1 4 1 63).toInstrSpec (shr_r64_imm8_effect_step 0x109ea1 0x48 0xe9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x109ea5 [0x48, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x109ea5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ea5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ea5 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ea5 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109ea5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x109eaa [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x109eaa) (leaR64Effect 0x109eaa 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x109eaa 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x109eaa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x109eaf [0x31, 0xC9] (fun s => s.RIP = 0x109eaf) (xorR32R32Effect 0x109eaf 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109eaf 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x109eaf 0xc9 (by decide)) pre_rip
  have f24 : InstrSpec 0x109eb1 [0x31, 0xD2] (fun s => s.RIP = 0x109eb1) (xorR32R32Effect 0x109eb1 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109eb1 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x109eb1 0xd2 (by decide)) pre_rip
  have f25 : InstrSpec 0x109eb3 [0x48, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x109eb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109eb3 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109eb3 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109eb3 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109eb3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x109eb8 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x109eb8) (sarR64Effect 0x109eb8 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x109eb8 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x109eb8 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x109ebc [0x48, 0xBE, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x109ebc) (movR64Imm64Effect 0x109ebc 6 0x4551231950b75fc5)
      [] [] [.reg 6, .rip] :=
    (movR64Imm64Effect_footprint 0x109ebc 6 0x4551231950b75fc5).toInstrSpec (mov_r64_imm64_effect_step 0x109ebc 0x48 0xbe (by decide) (by decide) 0x4551231950b75fc5) pre_rip
  have f28 : InstrSpec 0x109ec6 [0x4C, 0x01, 0xE6] (fun s => s.RIP = 0x109ec6) (addR64R64Effect 0x109ec6 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109ec6 6 12).toInstrSpec (add_r64_r64_effect_step 0x109ec6 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x109ec9 [0x48, 0x01, 0xD6] (fun s => s.RIP = 0x109ec9) (addR64R64Effect 0x109ec9 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109ec9 6 2).toInstrSpec (add_r64_r64_effect_step 0x109ec9 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x109ecc [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x109ecc) (movR64R64Effect 0x109ecc 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x109ecc 2 12).toInstrSpec (mov_r64_r64_effect_step 0x109ecc 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x109ecf [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x109ecf) (notR64Effect 0x109ecf 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x109ecf 2).toInstrSpec (not_r64_effect_step 0x109ecf 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x109ed2 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x109ed2) (orR64R64Effect 0x109ed2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109ed2 2 6).toInstrSpec (or_r64_r64_effect_step 0x109ed2 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x109ed5 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x109ed5) (shrR64Effect 0x109ed5 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x109ed5 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x109ed5 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x109ed9 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x109ed9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ed9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ed9 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ed9 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109ed9 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x109ede [0x31, 0xD2] (fun s => s.RIP = 0x109ede) (xorR32R32Effect 0x109ede 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x109ede 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x109ede 0xd2 (by decide)) pre_rip
  have f36 : InstrSpec 0x109ee0 [0x48, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x109ee0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ee0 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109ee0 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x109ee0 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x109ee0 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x109ee5 [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x109ee5) (sarR64Effect 0x109ee5 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x109ee5 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x109ee5 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x109ee9 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x109ee9) (movR64R64Effect 0x109ee9 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x109ee9 6 15).toInstrSpec (mov_r64_r64_effect_step 0x109ee9 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x109eec [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x109eec) (notR64Effect 0x109eec 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x109eec 6).toInstrSpec (not_r64_effect_step 0x109eec 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 85), (1, 93), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ea5) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 85), (1, 93), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eaa) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(1, 93), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eaf) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(1, 97), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eb1) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(1, 97), (2, 99), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eb3) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(1, 97), (2, 101), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eb8) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(1, 97), (2, 103), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ebc) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(1, 97), (2, 103), (3, 65), (4, 63), (5, 5), (6, 105), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ec6) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(1, 97), (2, 103), (3, 65), (4, 63), (5, 5), (6, 107), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ec9) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(1, 97), (2, 103), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ecc) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(1, 97), (2, 111), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ecf) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(1, 97), (2, 113), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed2) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(1, 97), (2, 115), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed5) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(1, 97), (2, 117), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ed9) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(1, 97), (2, 117), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ede) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(1, 97), (2, 120), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee0) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(1, 97), (2, 122), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee5) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(1, 97), (2, 124), (3, 65), (4, 63), (5, 5), (6, 109), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ee9) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f38 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(1, 97), (2, 124), (3, 65), (4, 63), (5, 5), (6, 126), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eec) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f39 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(1, 97), (2, 124), (3, 65), (4, 63), (5, 5), (6, 128), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109eef) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109e60_2 code

theorem rest_l109e60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109e60 bytes_l109e60) (entryMap (live .l109e60))
      58 0x109e60 bytes_l109e60 b_l109e60 := by
  have f0 : InstrSpec 0x109e60 [0x41, 0x57] (PushPre 0x109e60 2) (pushR64Effect 0x109e60 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e60 2 15).toInstrSpec (push_r64_rex_effect_step 0x109e60 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x109e62 [0x41, 0x56] (PushPre 0x109e62 2) (pushR64Effect 0x109e62 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e62 2 14).toInstrSpec (push_r64_rex_effect_step 0x109e62 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109e64 [0x41, 0x55] (PushPre 0x109e64 2) (pushR64Effect 0x109e64 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e64 2 13).toInstrSpec (push_r64_rex_effect_step 0x109e64 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109e66 [0x41, 0x54] (PushPre 0x109e66 2) (pushR64Effect 0x109e66 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e66 2 12).toInstrSpec (push_r64_rex_effect_step 0x109e66 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109e68 [0x53] (PushPre 0x109e68 1) (pushR64Effect 0x109e68 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109e68 1 3).toInstrSpec (push_r64_effect_step 0x109e68 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109e69 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x109e69) (subR64Imm8Effect 0x109e69 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x109e69 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x109e69 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109e6d [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x109e6d) (movR64R64Effect 0x109e6d 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x109e6d 3 7).toInstrSpec (mov_r64_r64_effect_step 0x109e6d 0x48 0xfb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109e70 [0x4C, 0x8B, 0x36] (LoadPre 0x109e70 (fun s => AddrMode.addr (.base 6 .none) s (0x109e70 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109e70 14 (.base 6 .none))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x109e70 14 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109e70 0x4c (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109e73 [0x4C, 0x8B, 0x7E, 0x08] (LoadPre 0x109e73 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109e73 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e73 15 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x109e73 15 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109e73 0x4c (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x109e77 [0x49, 0x0F, 0xCE] (fun s => s.RIP = 0x109e77) (bswapR64Effect 0x109e77 3 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (bswapR64Effect_footprint 0x109e77 3 14).toInstrSpec (bswap_r64_effect_step 0x109e77 0x49 (by decide) 0xce (by decide)) pre_rip
  have f10 : InstrSpec 0x109e7a [0x49, 0x0F, 0xCF] (fun s => s.RIP = 0x109e7a) (bswapR64Effect 0x109e7a 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (bswapR64Effect_footprint 0x109e7a 3 15).toInstrSpec (bswap_r64_effect_step 0x109e7a 0x49 (by decide) 0xcf (by decide)) pre_rip
  have f11 : InstrSpec 0x109e7d [0x4C, 0x8B, 0x66, 0x10] (LoadPre 0x109e7d (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109e7d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e7d 12 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x109e7d 12 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109e7d 0x4c (by decide) 4 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x109e81 [0x49, 0x0F, 0xCC] (fun s => s.RIP = 0x109e81) (bswapR64Effect 0x109e81 3 12)
      [.gpr 12] [] [.reg 12, .rip] :=
    (bswapR64Effect_footprint 0x109e81 3 12).toInstrSpec (bswap_r64_effect_step 0x109e81 0x49 (by decide) 0xcc (by decide)) pre_rip
  have f13 : InstrSpec 0x109e84 [0x4C, 0x8B, 0x6E, 0x18] (LoadPre 0x109e84 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109e84 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e84 13 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x109e84 13 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109e84 0x4c (by decide) 5 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x109e88 [0x49, 0x0F, 0xCD] (fun s => s.RIP = 0x109e88) (bswapR64Effect 0x109e88 3 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (bswapR64Effect_footprint 0x109e88 3 13).toInstrSpec (bswap_r64_effect_step 0x109e88 0x49 (by decide) 0xcd (by decide)) pre_rip
  have f15 : InstrSpec 0x109e8b [0x48, 0xB8, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40] (fun s => s.RIP = 0x109e8b) (movR64Imm64Effect 0x109e8b 0 0x402da1732fc9bebf)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x109e8b 0 0x402da1732fc9bebf).toInstrSpec (mov_r64_imm64_effect_step 0x109e8b 0x48 0xb8 (by decide) (by decide) 0x402da1732fc9bebf) pre_rip
  have f16 : InstrSpec 0x109e95 [0x4C, 0x01, 0xE8] (fun s => s.RIP = 0x109e95) (addR64R64Effect 0x109e95 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x109e95 0 13).toInstrSpec (add_r64_r64_effect_step 0x109e95 0x4c 0xe8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x109e98 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x109e98) (movR64R64Effect 0x109e98 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x109e98 1 13).toInstrSpec (mov_r64_r64_effect_step 0x109e98 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x109e9b [0x48, 0xF7, 0xD1] (fun s => s.RIP = 0x109e9b) (notR64Effect 0x109e9b 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR64Effect_footprint 0x109e9b 1).toInstrSpec (not_r64_effect_step 0x109e9b 0x48 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x109e9e [0x48, 0x09, 0xC1] (fun s => s.RIP = 0x109e9e) (orR64R64Effect 0x109e9e 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (orR64R64Effect_footprint 0x109e9e 1 0).toInstrSpec (or_r64_r64_effect_step 0x109e9e 0x48 0xc1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e62) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e64) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e66) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e68) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e69) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e6d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e70) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e73) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e77) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e7a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e7d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 75), (13, 13), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e81) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 13), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e84) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 79), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e88) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e8b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e95) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e98) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (1, 87), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e9b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 85), (1, 89), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109e9e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 85), (1, 91), (2, 2), (3, 65), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ea1) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109e60_1 code

theorem block_l109e60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109e60 :=
  Rest.liftedBlock (rest_l109e60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109e60 x hx)

theorem rest_l109f32 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109f32 bytes_l109f32) (entryMap (live .l109f32))
      13 0x109f32 bytes_l109f32 b_l109f32 := by
  have f0 : InstrSpec 0x109f32 [0x4C, 0x89, 0x2B] (StorePre 0x109f32 3 (fun s => AddrMode.addr (.base 3 .none) s (0x109f32 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109f32 13 (.base 3 .none))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f32 13 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x109f32 0x4c (by decide) 5 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x109f35 [0x4C, 0x89, 0x63, 0x08] (StorePre 0x109f35 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x109f35 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f35 12 (.base 3 (.d8 0x8)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f35 12 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109f35 0x4c (by decide) 4 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x109f39 [0x4C, 0x89, 0x7B, 0x10] (StorePre 0x109f39 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x109f39 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f39 15 (.base 3 (.d8 0x10)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f39 15 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109f39 0x4c (by decide) 7 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x109f3d [0x4C, 0x89, 0x73, 0x18] (StorePre 0x109f3d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x109f3d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f3d 14 (.base 3 (.d8 0x18)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x109f3d 14 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109f3d 0x4c (by decide) 6 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x109f41 [0x88, 0x43, 0x20] (StorePre 0x109f41 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x109f41 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f41 3 0 (.base 3 (.d8 0x20)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x109f41 3 0 (.base 3 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x109f41 0 (by decide) (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x109f44 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x109f44) (movR64R64Effect 0x109f44 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x109f44 0 3).toInstrSpec (mov_r64_r64_effect_step 0x109f44 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x109f47 [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x109f47) (addR64Imm8Effect 0x109f47 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109f47 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x109f47 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109f4b [0x5B] (PopPre 0x109f4b) (popR64Effect 0x109f4b 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f4b 1 3).toInstrSpec (pop_r64_effect_step 0x109f4b 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x109f4c [0x41, 0x5C] (PopPre 0x109f4c) (popR64Effect 0x109f4c 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f4c 2 12).toInstrSpec (pop_r64_rex_effect_step 0x109f4c 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x109f4e [0x41, 0x5D] (PopPre 0x109f4e) (popR64Effect 0x109f4e 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f4e 2 13).toInstrSpec (pop_r64_rex_effect_step 0x109f4e 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x109f50 [0x41, 0x5E] (PopPre 0x109f50) (popR64Effect 0x109f50 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f50 2 14).toInstrSpec (pop_r64_rex_effect_step 0x109f50 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x109f52 [0x41, 0x5F] (PopPre 0x109f52) (popR64Effect 0x109f52 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109f52 2 15).toInstrSpec (pop_r64_rex_effect_step 0x109f52 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x109f54 [0xC3] (RetPre 0x109f54) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109f54).toInstrSpec (ret_effect_step 0x109f54) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f35) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f39) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f3d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f41) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f44) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f47) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f4b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 64) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f4c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f4e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f50) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 72), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 71), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f52) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 75) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 75), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109f54) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 79) (ρ' := [(0, 58), (1, 1), (2, 2), (3, 62), (4, 78), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) f12 (by decide) rfl rfl rfl (by decide)

theorem block_l109f32 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109f32 :=
  Rest.liftedBlock (rest_l109f32 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109f32 x hx)

theorem rest_l10a220_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x10a220 bytes_l10a220) [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x10a263 bytes_l10a220_1 b_l10a220_1 := by
  have f20 : InstrSpec 0x10a263 [0x48, 0x0F, 0x45, 0xF2] (fun s => s.RIP = 0x10a263) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a263 4 6 2))
      [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x10a263 4 6 2 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a263 5 0x48 (by decide) 0xf2 (by decide) c)) pre_rip
  have f21 : InstrSpec 0x10a267 [0x48, 0x89, 0x38] (StorePre 0x10a267 3 (fun s => AddrMode.addr (.base 0 .none) s (0x10a267 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a267 7 (.base 0 .none))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a267 7 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10a267 0x48 (by decide) 7 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x10a26a [0x4C, 0x89, 0x40, 0x08] (StorePre 0x10a26a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10a26a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a26a 8 (.base 0 (.d8 0x8)))
      [.gpr 8, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a26a 8 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10a26a 0x4c (by decide) 0 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x10a26e [0x4C, 0x89, 0x48, 0x10] (StorePre 0x10a26e 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10a26e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a26e 9 (.base 0 (.d8 0x10)))
      [.gpr 9, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a26e 9 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10a26e 0x4c (by decide) 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10a272 [0x48, 0x89, 0x70, 0x18] (StorePre 0x10a272 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10a272 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a272 6 (.base 0 (.d8 0x18)))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a272 6 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10a272 0x48 (by decide) 6 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x10a276 [0x48, 0x83, 0xC4, 0x01] (fun s => s.RIP = 0x10a276) (addR64Imm8Effect 0x10a276 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10a276 4 0x1).toInstrSpec (add_r64_imm8_effect_step 0x10a276 0x48 0xc4 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10a27a [0xC3] (RetPre 0x10a27a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10a27a).toInstrSpec (ret_effect_step 0x10a27a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a267) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a26a) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.exec (n := 94) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a26e) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a272) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a276) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 97), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a27a) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f26 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 101) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 100), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f26 (by decide) rfl rfl rfl (by decide)

theorem rest_l10a220 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a220 bytes_l10a220) (entryMap (live .l10a220))
      27 0x10a220 bytes_l10a220 b_l10a220 := by
  have f0 : InstrSpec 0x10a220 [0x48, 0x83, 0xEC, 0x01] (fun s => s.RIP = 0x10a220) (subR64Imm8Effect 0x10a220 4 0x1)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10a220 4 0x1).toInstrSpec (sub_r64_imm8_effect_step 0x10a220 0x48 0xec 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10a224 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x10a224) (movR64R64Effect 0x10a224 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10a224 0 7).toInstrSpec (mov_r64_r64_effect_step 0x10a224 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a227 [0x48, 0x8B, 0x3E] (LoadPre 0x10a227 (fun s => AddrMode.addr (.base 6 .none) s (0x10a227 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a227 7 (.base 6 .none))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10a227 7 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10a227 0x48 (by decide) 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10a22a [0x4C, 0x8B, 0x46, 0x08] (LoadPre 0x10a22a (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a22a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a22a 8 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10a22a 8 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10a22a 0x4c (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10a22e [0x4C, 0x8B, 0x4E, 0x10] (LoadPre 0x10a22e (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a22e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a22e 9 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10a22e 9 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a22e 0x4c (by decide) 1 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10a232 [0x48, 0x8B, 0x76, 0x18] (LoadPre 0x10a232 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a232 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a232 6 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10a232 6 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a232 0x48 (by decide) 6 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10a236 [0x88, 0x0C, 0x24] (StorePre 0x10a236 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a236 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a236 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10a236 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x10a236 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10a239 [0x48, 0x89, 0xE1] (fun s => s.RIP = 0x10a239) (movR64R64Effect 0x10a239 1 4)
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10a239 1 4).toInstrSpec (mov_r64_r64_effect_step 0x10a239 0x48 0xe1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10a23c [0x0F, 0xB6, 0x0C, 0x24] (LoadPre 0x10a23c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a23c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a23c 4 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a23c 4 1 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x10a23c 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10a240 [0x4C, 0x8B, 0x12] (LoadPre 0x10a240 (fun s => AddrMode.addr (.base 2 .none) s (0x10a240 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a240 10 (.base 2 .none))
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10a240 10 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10a240 0x4c (by decide) 2 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10a243 [0x4C, 0x8B, 0x5A, 0x08] (LoadPre 0x10a243 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x10a243 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a243 11 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x10a243 11 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10a243 0x4c (by decide) 3 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10a247 [0x84, 0xC9] (fun s => s.RIP = 0x10a247) (testR8R8Effect 0x10a247 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a247 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a247 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10a249 [0x49, 0x0F, 0x45, 0xFA] (fun s => s.RIP = 0x10a249) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a249 4 7 10))
      [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (cmovR64R64Effect_footprint 0x10a249 4 7 10 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a249 5 0x49 (by decide) 0xfa (by decide) c)) pre_rip
  have f13 : InstrSpec 0x10a24d [0x84, 0xC9] (fun s => s.RIP = 0x10a24d) (testR8R8Effect 0x10a24d 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a24d 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a24d 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10a24f [0x4D, 0x0F, 0x45, 0xC3] (fun s => s.RIP = 0x10a24f) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a24f 4 8 11))
      [.gpr 8, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x10a24f 4 8 11 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a24f 5 0x4d (by decide) 0xc3 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x10a253 [0x4C, 0x8B, 0x52, 0x10] (LoadPre 0x10a253 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x10a253 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a253 10 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x10a253 10 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a253 0x4c (by decide) 2 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10a257 [0x84, 0xC9] (fun s => s.RIP = 0x10a257) (testR8R8Effect 0x10a257 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a257 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a257 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10a259 [0x4D, 0x0F, 0x45, 0xCA] (fun s => s.RIP = 0x10a259) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a259 4 9 10))
      [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 9, .rip] :=
    (cmovR64R64Effect_footprint 0x10a259 4 9 10 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x10a259 5 0x4d (by decide) 0xca (by decide) c)) pre_rip
  have f18 : InstrSpec 0x10a25d [0x48, 0x8B, 0x52, 0x18] (LoadPre 0x10a25d (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x10a25d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a25d 2 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10a25d 2 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10a25d 0x48 (by decide) 2 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10a261 [0x84, 0xC9] (fun s => s.RIP = 0x10a261) (testR8R8Effect 0x10a261 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x10a261 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x10a261 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a224) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a227) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a22a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 57), (8, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a22e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a232) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a236) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a239) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a23c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a240) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (10, 69), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a243) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a247) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 57), (8, 59), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a249) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 59), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a24d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 59), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a24f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 61), (10, 69), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a253) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 61), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a257) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 61), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a259) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a25d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a261) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 55), (1, 67), (2, 87), (3, 3), (4, 53), (5, 5), (6, 63), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (19, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a263) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a220_1 code

theorem block_l10a220 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a220 :=
  Rest.liftedBlock (rest_l10a220 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a220 x hx)

theorem rest_l10a280 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a280 bytes_l10a280) (entryMap (live .l10a280))
      5 0x10a280 bytes_l10a280 b_l10a280 := by
  have f0 : InstrSpec 0x10a280 [0x50] (PushPre 0x10a280 1) (pushR64Effect 0x10a280 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10a280 1 0).toInstrSpec (push_r64_effect_step 0x10a280 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10a281 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10a281) (movR64R64Effect 0x10a281 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a281 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10a281 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a284 [0xBE, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a284) (movR32Imm32Effect 0x10a284 5 6 0x4)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a284 5 6 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10a284 0xbe (by decide) 0x4) pre_rip
  have f3 : InstrSpec 0x10a289 [0xB9, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a289) (movR32Imm32Effect 0x10a289 5 1 0x4)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10a289 5 1 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x10a289 0xb9 (by decide) 0x4) pre_rip
  have f4 : InstrSpec 0x10a28e [0xE8, 0xBD, 0xDC, 0x01, 0x00] (PushPre 0x10a28e 5) (callEffect (fun _ => 0x127f50) 0x10a293)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a28e 0x127f50 0x10a293).toInstrSpec (call_rel32_effect_step 0x10a28e 0x1dcbd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a281) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a284) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 53), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a289) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 53), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a28e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 59), (2, 55), (3, 3), (4, 61), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f50) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10a280 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a280 :=
  Rest.liftedBlock (rest_l10a280 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a280 x hx)

theorem rest_l10a293 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a293 bytes_l10a293) (entryMap (live .l10a293))
      4 0x10a293 bytes_l10a293 b_l10a293 := by
  have f0 : InstrSpec 0x10a293 [0x24, 0x01] (fun s => s.RIP = 0x10a293) (andAlImm8Effect 0x10a293 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x10a293 0x1).toInstrSpec (and_al_imm8_effect_step 0x10a293 0x1) pre_rip
  have f1 : InstrSpec 0x10a295 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x10a295) (movzxR32R8Effect 0x10a295 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x10a295 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x10a295 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a298 [0x58] (PopPre 0x10a298) (popR64Effect 0x10a298 1 0)
      [.gpr 4] [] [.reg 0, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a298 1 0).toInstrSpec (pop_r64_effect_step 0x10a298 0x58 (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a295) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a298) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a299) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x10a299 0x1dab2 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10a293 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a293 :=
  Rest.liftedBlock (rest_l10a293 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a293 x hx)

theorem rest_l10fa10_1 [Bindings] (code : CodeMap) :
    Rest (n := 88) code lifted (codeRange 0x10fa10 bytes_l10fa10) [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      5 0x10fa54 bytes_l10fa10_1 b_l10fa10_1 := by
  have f20 : InstrSpec 0x10fa54 [0x4C, 0x8B, 0x76, 0x10] (LoadPre 0x10fa54 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10fa54 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa54 14 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10fa54 14 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10fa54 0x4c (by decide) 6 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10fa58 [0x4C, 0x8B, 0x7E, 0x18] (LoadPre 0x10fa58 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10fa58 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa58 15 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10fa58 15 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10fa58 0x4c (by decide) 7 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x10fa5c [0x4C, 0x8B, 0x66, 0x20] (LoadPre 0x10fa5c (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x10fa5c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa5c 12 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10fa5c 12 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10fa5c 0x4c (by decide) 4 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x10fa60 [0x8B, 0x7E, 0x50] (LoadPre 0x10fa60 (fun s => AddrMode.addr (.base 6 (.d8 0x50)) s (0x10fa60 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x10fa60 7 (.base 6 (.d8 0x50)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x10fa60 7 (.base 6 (.d8 0x50))).toInstrSpec (mov_r32_m32_low_effect_step 0x10fa60 7 (.base 6 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10fa63 [0xE8, 0xE8, 0x82, 0x01, 0x00] (PushPre 0x10fa63 5) (callEffect (fun _ => 0x127d50) 0x10fa68)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10fa63 0x127d50 0x10fa68).toInstrSpec (call_rel32_effect_step 0x10fa63 0x182e8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f20 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 88), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa58) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 88), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa5c) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 92), (13, 84), (14, 88), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa60) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 94), (8, 8), (9, 9), (10, 10), (11, 11), (12, 92), (13, 84), (14, 88), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa63) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 96), (5, 86), (6, 6), (7, 94), (8, 8), (9, 9), (10, 10), (11, 11), (12, 92), (13, 84), (14, 88), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f24 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 98) (by decide) (by decide) rfl rfl

theorem rest_l10fa10 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fa10 bytes_l10fa10) (entryMap (live .l10fa10))
      25 0x10fa10 bytes_l10fa10 b_l10fa10 := by
  have f0 : InstrSpec 0x10fa10 [0x55] (PushPre 0x10fa10 1) (pushR64Effect 0x10fa10 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa10 1 5).toInstrSpec (push_r64_effect_step 0x10fa10 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10fa11 [0x41, 0x57] (PushPre 0x10fa11 2) (pushR64Effect 0x10fa11 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa11 2 15).toInstrSpec (push_r64_rex_effect_step 0x10fa11 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10fa13 [0x41, 0x56] (PushPre 0x10fa13 2) (pushR64Effect 0x10fa13 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa13 2 14).toInstrSpec (push_r64_rex_effect_step 0x10fa13 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10fa15 [0x41, 0x55] (PushPre 0x10fa15 2) (pushR64Effect 0x10fa15 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa15 2 13).toInstrSpec (push_r64_rex_effect_step 0x10fa15 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10fa17 [0x41, 0x54] (PushPre 0x10fa17 2) (pushR64Effect 0x10fa17 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa17 2 12).toInstrSpec (push_r64_rex_effect_step 0x10fa17 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10fa19 [0x53] (PushPre 0x10fa19 1) (pushR64Effect 0x10fa19 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fa19 1 3).toInstrSpec (push_r64_effect_step 0x10fa19 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10fa1a [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x10fa1a) (subR64Imm8Effect 0x10fa1a 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10fa1a 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x10fa1a 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10fa1e [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10fa1e) (movR64R64Effect 0x10fa1e 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10fa1e 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10fa1e 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10fa21 [0x48, 0x8B, 0x46, 0x28] (LoadPre 0x10fa21 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x10fa21 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa21 0 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa21 0 (.base 6 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10fa21 0x48 (by decide) 0 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10fa25 [0x48, 0x89, 0x04, 0x24] (StorePre 0x10fa25 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fa25 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fa25 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa25 0 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10fa25 0x48 (by decide) 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10fa29 [0x48, 0x8B, 0x46, 0x30] (LoadPre 0x10fa29 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x10fa29 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa29 0 (.base 6 (.d8 0x30)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa29 0 (.base 6 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10fa29 0x48 (by decide) 0 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10fa2d [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x10fa2d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fa2d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa2d 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa2d 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10fa2d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10fa32 [0x48, 0x8B, 0x46, 0x38] (LoadPre 0x10fa32 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x10fa32 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa32 0 (.base 6 (.d8 0x38)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa32 0 (.base 6 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10fa32 0x48 (by decide) 0 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10fa36 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10fa36 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fa36 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa36 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa36 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10fa36 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10fa3b [0x48, 0x8B, 0x46, 0x40] (LoadPre 0x10fa3b (fun s => AddrMode.addr (.base 6 (.d8 0x40)) s (0x10fa3b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa3b 0 (.base 6 (.d8 0x40)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa3b 0 (.base 6 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10fa3b 0x48 (by decide) 0 (.base 6 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10fa3f [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x10fa3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10fa3f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa3f 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa3f 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10fa3f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x10fa44 [0x48, 0x8B, 0x46, 0x48] (LoadPre 0x10fa44 (fun s => AddrMode.addr (.base 6 (.d8 0x48)) s (0x10fa44 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa44 0 (.base 6 (.d8 0x48)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10fa44 0 (.base 6 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10fa44 0x48 (by decide) 0 (.base 6 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10fa48 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10fa48 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10fa48 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fa48 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fa48 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10fa48 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10fa4d [0x4C, 0x8B, 0x2E] (LoadPre 0x10fa4d (fun s => AddrMode.addr (.base 6 .none) s (0x10fa4d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10fa4d 13 (.base 6 .none))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10fa4d 13 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10fa4d 0x4c (by decide) 5 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10fa50 [0x48, 0x8B, 0x6E, 0x08] (LoadPre 0x10fa50 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10fa50 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa50 5 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10fa50 5 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10fa50 0x48 (by decide) 5 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa11) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa13) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa15) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa17) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa19) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa1a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa1e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa21) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa25) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa29) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa2d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa32) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa36) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa3b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa3f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa44) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa48) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa4d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f18 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa50) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f19 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 81), (1, 1), (2, 2), (3, 67), (4, 65), (5, 86), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 84), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa54) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fa10_1 code

theorem block_l10fa10 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fa10 :=
  Rest.liftedBlock (rest_l10fa10 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fa10 x hx)

theorem rest_l10fa68_2 [Bindings] (code : CodeMap) :
    Rest (n := 118) code lifted (codeRange 0x10fa68 bytes_l10fa68) [(0, 114), (1, 97), (2, 81), (3, 3), (4, 116), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x10fb08 bytes_l10fa68_2 b_l10fa68_2 := by
  have f40 : InstrSpec 0x10fb08 [0x5B] (PopPre 0x10fb08) (popR64Effect 0x10fb08 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb08 1 3).toInstrSpec (pop_r64_effect_step 0x10fb08 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f41 : InstrSpec 0x10fb09 [0x41, 0x5C] (PopPre 0x10fb09) (popR64Effect 0x10fb09 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb09 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10fb09 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f42 : InstrSpec 0x10fb0b [0x41, 0x5D] (PopPre 0x10fb0b) (popR64Effect 0x10fb0b 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb0b 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10fb0b 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f43 : InstrSpec 0x10fb0d [0x41, 0x5E] (PopPre 0x10fb0d) (popR64Effect 0x10fb0d 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb0d 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10fb0d 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f44 : InstrSpec 0x10fb0f [0x41, 0x5F] (PopPre 0x10fb0f) (popR64Effect 0x10fb0f 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb0f 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10fb0f 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f45 : InstrSpec 0x10fb11 [0x5D] (PopPre 0x10fb11) (popR64Effect 0x10fb11 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fb11 1 5).toInstrSpec (pop_r64_effect_step 0x10fb11 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f46 : InstrSpec 0x10fb12 [0xC3] (RetPre 0x10fb12) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10fb12).toInstrSpec (ret_effect_step 0x10fb12) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f40 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 119) f40 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 120) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 119), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb09) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f41 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 122) f41 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 123) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 122), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb0b) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f42 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 125) f42 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 126) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 125), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb0d) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f43 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f43 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 129) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 128), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 127), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb0f) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 131) f44 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 132) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 131), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 127), (15, 130), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb11) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f45 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 134) f45 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 135) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 134), (5, 133), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 127), (15, 130), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb12) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f46 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 137) f46 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 138) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 118), (4, 137), (5, 133), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 121), (13, 124), (14, 127), (15, 130), (22, 22), (39, 39), (50, 50), (51, 51)]) f46 (by decide) rfl rfl rfl (by decide)

theorem rest_l10fa68_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x10fa68 bytes_l10fa68) [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      27 0x10faab bytes_l10fa68_1 b_l10fa68_1 := by
  have f20 : InstrSpec 0x10faab [0x49, 0x21, 0xC0] (fun s => s.RIP = 0x10faab) (andR64R64Effect 0x10faab 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10faab 8 0).toInstrSpec (and_r64_r64_effect_step 0x10faab 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10faae [0x48, 0x23, 0x44, 0x24, 0x20] (LoadPre 0x10faae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10faae + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x10faae 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (andR64M64Effect_footprint 0x10faae 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (and_r64_m64_effect_step 0x10faae 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x10fab3 [0x83, 0xE1, 0x01] (fun s => s.RIP = 0x10fab3) (andR32Imm8Effect 0x10fab3 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x10fab3 3 1 0x1).toInstrSpec (and_r32_imm8_effect_step 0x10fab3 0xe1 0x1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10fab6 [0x4C, 0x89, 0x2B] (StorePre 0x10fab6 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10fab6 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10fab6 13 (.base 3 .none))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fab6 13 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10fab6 0x4c (by decide) 5 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10fab9 [0x48, 0x89, 0x6B, 0x08] (StorePre 0x10fab9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10fab9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fab9 5 (.base 3 (.d8 0x8)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fab9 5 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10fab9 0x48 (by decide) 5 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x10fabd [0x4C, 0x89, 0x73, 0x10] (StorePre 0x10fabd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10fabd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fabd 14 (.base 3 (.d8 0x10)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fabd 14 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10fabd 0x4c (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x10fac1 [0x4C, 0x89, 0x7B, 0x18] (StorePre 0x10fac1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10fac1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fac1 15 (.base 3 (.d8 0x18)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fac1 15 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10fac1 0x4c (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x10fac5 [0x4C, 0x89, 0x63, 0x20] (StorePre 0x10fac5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10fac5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fac5 12 (.base 3 (.d8 0x20)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fac5 12 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10fac5 0x4c (by decide) 4 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x10fac9 [0x48, 0x89, 0x53, 0x28] (StorePre 0x10fac9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10fac9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fac9 2 (.base 3 (.d8 0x28)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fac9 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10fac9 0x48 (by decide) 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x10facd [0x48, 0x89, 0x73, 0x30] (StorePre 0x10facd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x10facd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10facd 6 (.base 3 (.d8 0x30)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10facd 6 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10facd 0x48 (by decide) 6 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x10fad1 [0x48, 0x89, 0x7B, 0x38] (StorePre 0x10fad1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x10fad1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fad1 7 (.base 3 (.d8 0x38)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fad1 7 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x10fad1 0x48 (by decide) 7 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x10fad5 [0x4C, 0x89, 0x43, 0x40] (StorePre 0x10fad5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x10fad5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fad5 8 (.base 3 (.d8 0x40)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fad5 8 (.base 3 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x10fad5 0x4c (by decide) 0 (.base 3 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x10fad9 [0x48, 0x89, 0x43, 0x48] (StorePre 0x10fad9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x10fad9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fad9 0 (.base 3 (.d8 0x48)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fad9 0 (.base 3 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x10fad9 0x48 (by decide) 0 (.base 3 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x10fadd [0x48, 0x89, 0x4B, 0x50] (StorePre 0x10fadd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x10fadd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fadd 1 (.base 3 (.d8 0x50)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fadd 1 (.base 3 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x10fadd 0x48 (by decide) 1 (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x10fae1 [0x48, 0xC7, 0x43, 0x58, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fae1 8 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x10fae1 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fae1 (.base 3 (.d8 0x58)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fae1 (.base 3 (.d8 0x58)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fae1 0x48 (by decide) (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x10fae9 [0x48, 0xC7, 0x43, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fae9 8 (fun s => AddrMode.addr (.base 3 (.d8 0x60)) s (0x10fae9 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fae9 (.base 3 (.d8 0x60)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fae9 (.base 3 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fae9 0x48 (by decide) (.base 3 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x10faf1 [0x48, 0xC7, 0x43, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10faf1 8 (fun s => AddrMode.addr (.base 3 (.d8 0x68)) s (0x10faf1 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10faf1 (.base 3 (.d8 0x68)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10faf1 (.base 3 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10faf1 0x48 (by decide) (.base 3 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x10faf9 [0x48, 0xC7, 0x43, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10faf9 8 (fun s => AddrMode.addr (.base 3 (.d8 0x70)) s (0x10faf9 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10faf9 (.base 3 (.d8 0x70)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10faf9 (.base 3 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10faf9 0x48 (by decide) (.base 3 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x10fb01 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10fb01) (movR64R64Effect 0x10fb01 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10fb01 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10fb01 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10fb04 [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x10fb04) (addR64Imm8Effect 0x10fb04 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10fb04 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x10fb04 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faae) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 95), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fab3) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fab6) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fab9) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fabd) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fac1) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fac5) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fac9) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10facd) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fad1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fad5) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fad9) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.exec (n := 108) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fadd) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fae1) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fae9) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faf1) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faf9) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 95), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb01) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb04) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f39 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 114), (1, 97), (2, 81), (3, 3), (4, 116), (5, 73), (6, 85), (7, 89), (8, 93), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb08) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fa68_2 code

theorem rest_l10fa68 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fa68 bytes_l10fa68) (entryMap (live .l10fa68))
      47 0x10fa68 bytes_l10fa68 b_l10fa68 := by
  have f0 : InstrSpec 0x10fa68 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x10fa68) (movzxR32R8Effect 0x10fa68 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x10fa68 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x10fa68 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fa6b [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10fa6b) (movR64R64Effect 0x10fa6b 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10fa6b 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10fa6b 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10fa6e [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x10fa6e) (negR64Effect 0x10fa6e 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x10fa6e 1).toInstrSpec (neg_r64_effect_step 0x10fa6e 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10fa71 [0x48, 0x8B, 0x34, 0x24] (LoadPre 0x10fa71 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fa71 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fa71 6 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10fa71 6 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10fa71 0x48 (by decide) 6 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10fa75 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10fa75) (movR64R64Effect 0x10fa75 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10fa75 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10fa75 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10fa78 [0x48, 0x83, 0xF2, 0x01] (fun s => s.RIP = 0x10fa78) (xorR64Imm8Effect 0x10fa78 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x10fa78 2 0x1).toInstrSpec (xor_r64_imm8_effect_step 0x10fa78 0x48 0xf2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10fa7c [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x10fa7c) (andR64R64Effect 0x10fa7c 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa7c 2 1).toInstrSpec (and_r64_r64_effect_step 0x10fa7c 0x48 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10fa7f [0xF7, 0xD1] (fun s => s.RIP = 0x10fa7f) (notR32Effect 0x10fa7f 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR32Effect_footprint 0x10fa7f 2 1).toInstrSpec (not_r32_effect_step 0x10fa7f 0xd1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10fa81 [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x10fa81) (decR64Effect 0x10fa81 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x10fa81 0).toInstrSpec (dec_r64_effect_step 0x10fa81 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10fa84 [0x49, 0x21, 0xC5] (fun s => s.RIP = 0x10fa84) (andR64R64Effect 0x10fa84 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa84 13 0).toInstrSpec (and_r64_r64_effect_step 0x10fa84 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10fa87 [0x48, 0x21, 0xC5] (fun s => s.RIP = 0x10fa87) (andR64R64Effect 0x10fa87 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa87 5 0).toInstrSpec (and_r64_r64_effect_step 0x10fa87 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10fa8a [0x49, 0x21, 0xC6] (fun s => s.RIP = 0x10fa8a) (andR64R64Effect 0x10fa8a 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa8a 14 0).toInstrSpec (and_r64_r64_effect_step 0x10fa8a 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10fa8d [0x49, 0x21, 0xC7] (fun s => s.RIP = 0x10fa8d) (andR64R64Effect 0x10fa8d 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa8d 15 0).toInstrSpec (and_r64_r64_effect_step 0x10fa8d 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10fa90 [0x49, 0x21, 0xC4] (fun s => s.RIP = 0x10fa90) (andR64R64Effect 0x10fa90 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa90 12 0).toInstrSpec (and_r64_r64_effect_step 0x10fa90 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10fa93 [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x10fa93) (xorR64R64Effect 0x10fa93 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10fa93 2 6).toInstrSpec (xor_r64_r64_effect_step 0x10fa93 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10fa96 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x10fa96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fa96 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fa96 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10fa96 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x10fa96 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10fa9b [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x10fa9b) (andR64R64Effect 0x10fa9b 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fa9b 6 0).toInstrSpec (and_r64_r64_effect_step 0x10fa9b 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10fa9e [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x10fa9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fa9e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fa9e 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10fa9e 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10fa9e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10faa3 [0x48, 0x21, 0xC7] (fun s => s.RIP = 0x10faa3) (andR64R64Effect 0x10faa3 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10faa3 7 0).toInstrSpec (and_r64_r64_effect_step 0x10faa3 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x10faa6 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x10faa6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10faa6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10faa6 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10faa6 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10faa6 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa6b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa6e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa71) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa75) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa78) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa7c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 57), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa7f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa81) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa84) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa87) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa8a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa8d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa90) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 69), (1, 67), (2, 65), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa93) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa96) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 83), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa9b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fa9e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 87), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faa3) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faa6) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 69), (1, 67), (2, 81), (3, 3), (4, 4), (5, 73), (6, 85), (7, 89), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10faab) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fa68_1 code

theorem block_l10fa68 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fa68 :=
  Rest.liftedBlock (rest_l10fa68 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fa68 x hx)

theorem rest_l10fe50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fe50 bytes_l10fe50) (entryMap (live .l10fe50))
      1 0x10fe50 bytes_l10fe50 b_l10fe50 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x10fe50 0xffffee8b (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10fe50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fe50 :=
  Rest.liftedBlock (rest_l10fe50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fe50 x hx)

theorem rest_l10ff00 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ff00 bytes_l10ff00) (entryMap (live .l10ff00))
      11 0x10ff00 bytes_l10ff00 b_l10ff00 := by
  have f0 : InstrSpec 0x10ff00 [0x55] (PushPre 0x10ff00 1) (pushR64Effect 0x10ff00 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff00 1 5).toInstrSpec (push_r64_effect_step 0x10ff00 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10ff01 [0x41, 0x57] (PushPre 0x10ff01 2) (pushR64Effect 0x10ff01 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff01 2 15).toInstrSpec (push_r64_rex_effect_step 0x10ff01 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10ff03 [0x41, 0x56] (PushPre 0x10ff03 2) (pushR64Effect 0x10ff03 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff03 2 14).toInstrSpec (push_r64_rex_effect_step 0x10ff03 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10ff05 [0x41, 0x55] (PushPre 0x10ff05 2) (pushR64Effect 0x10ff05 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff05 2 13).toInstrSpec (push_r64_rex_effect_step 0x10ff05 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10ff07 [0x41, 0x54] (PushPre 0x10ff07 2) (pushR64Effect 0x10ff07 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff07 2 12).toInstrSpec (push_r64_rex_effect_step 0x10ff07 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10ff09 [0x53] (PushPre 0x10ff09 1) (pushR64Effect 0x10ff09 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10ff09 1 3).toInstrSpec (push_r64_effect_step 0x10ff09 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10ff0a [0x48, 0x81, 0xEC, 0x48, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10ff0a) (subR64Imm32Effect 0x10ff0a 4 0x148)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10ff0a 4 0x148).toInstrSpec (sub_r64_imm32_effect_step 0x10ff0a 0x48 0xec 0x148 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10ff11 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x10ff11) (movR64R64Effect 0x10ff11 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10ff11 3 7).toInstrSpec (mov_r64_r64_effect_step 0x10ff11 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ff14 [0x4C, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ff14) (leaR64Effect 0x10ff14 14 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x10ff14 14 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (lea_r64_effect_step 0x10ff14 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10ff1c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10ff1c) (movR64R64Effect 0x10ff1c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10ff1c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10ff1c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ff1f [0xE8, 0x0C, 0x10, 0x01, 0x00] (PushPre 0x10ff1f 5) (callEffect (fun _ => 0x120f30) 0x10ff24)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ff1f 0x120f30 0x10ff24).toInstrSpec (call_rel32_effect_step 0x10ff1f 0x1100c (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff01) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff03) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff05) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff07) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff09) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff0a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff11) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff14) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff1c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (3, 67), (4, 65), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff1f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (3, 67), (4, 73), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f30) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l10ff00 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ff00 :=
  Rest.liftedBlock (rest_l10ff00 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ff00 x hx)

theorem rest_l10ff24 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ff24 bytes_l10ff24) (entryMap (live .l10ff24))
      11 0x10ff24 bytes_l10ff24 b_l10ff24 := by
  have f0 : InstrSpec 0x10ff24 [0x48, 0x8D, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ff24) (leaR64Effect 0x10ff24 0 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10ff24 0 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (lea_r64_effect_step 0x10ff24 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10ff2c [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10ff2c) (movR32Imm32Effect 0x10ff2c 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x10ff2c 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x10ff2c 0xb9 (by decide) 0xb) pre_rip
  have f2 : InstrSpec 0x10ff31 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x10ff31) (movR64R64Effect 0x10ff31 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10ff31 7 0).toInstrSpec (mov_r64_r64_effect_step 0x10ff31 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10ff34 [0x48, 0xC7, 0xC6, 0x70, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x10ff34) (movR64Imm32Effect 0x10ff34 6 0x202b70)
      [] [] [.reg 6, .rip] :=
    (movR64Imm32Effect_footprint 0x10ff34 6 0x202b70).toInstrSpec (mov_r64_imm32_effect_step 0x10ff34 0x48 0xc6 (by decide) (by decide) (by decide) 0x202b70) pre_rip
  have f4 : InstrSpec 0x10ff3b [0xF3, 0x48, 0xA5] (RepPre 0x10ff3b (RepMovsqPre 0x10ff3b)) (repMovsqEffect 0x10ff3b)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x10ff3b).toInstrSpecOfRuns (rep_movsq_runs hstride 0x10ff3b 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x10ff3e [0x8B, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x10ff3e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10ff3e + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10ff3e 1 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x10ff3e 1 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r32_m32_low_effect_step 0x10ff3e 1 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10ff45 [0x89, 0x4C, 0x24, 0x0C] (StorePre 0x10ff45 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10ff45 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10ff45 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10ff45 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x10ff45 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10ff49 [0x48, 0x8D, 0x7C, 0x24, 0x38] (fun s => s.RIP = 0x10ff49) (leaR64Effect 0x10ff49 7 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10ff49 7 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x10ff49 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ff4e [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x10ff4e) (movR64R64Effect 0x10ff4e 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10ff4e 6 0).toInstrSpec (mov_r64_r64_effect_step 0x10ff4e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10ff51 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x10ff51) (movR64R64Effect 0x10ff51 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10ff51 2 14).toInstrSpec (mov_r64_r64_effect_step 0x10ff51 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ff54 [0xE8, 0x17, 0x05, 0x01, 0x00] (PushPre 0x10ff54 5) (callEffect (fun _ => 0x120470) 0x10ff59)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ff54 0x120470 0x10ff59).toInstrSpec (call_rel32_effect_step 0x10ff54 0x10517 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff2c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff31) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff34) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff3b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff3e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 53), (1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff45) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff49) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 62), (3, 3), (4, 4), (5, 5), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff4e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 62), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff51) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 62), (2, 69), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff54) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 62), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120470) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 73) (by decide) (by decide) rfl rfl

theorem block_l10ff24 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ff24 :=
  Rest.liftedBlock (rest_l10ff24 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ff24 x hx)

theorem rest_l10ff59 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ff59 bytes_l10ff59) (entryMap (live .l10ff59))
      17 0x10ff59 bytes_l10ff59 b_l10ff59 := by
  have f0 : InstrSpec 0x10ff59 [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x10ff59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ff59 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff59 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff59 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x10ff59 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10ff5e [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x10ff5e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ff5e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff5e 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff5e 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10ff5e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10ff63 [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x10ff63 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ff63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff63 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff63 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x10ff63 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10ff68 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x10ff68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ff68 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff68 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff68 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10ff68 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10ff6d [0x48, 0x8B, 0x44, 0x24, 0x70] (LoadPre 0x10ff6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ff6d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff6d 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff6d 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x10ff6d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10ff72 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x10ff72 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ff72 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff72 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff72 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x10ff72 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10ff77 [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x10ff77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ff77 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff77 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff77 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x10ff77 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10ff7c [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x10ff7c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10ff7c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff7c 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff7c 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x10ff7c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10ff81 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x10ff81 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10ff81 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ff81 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x10ff81 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x10ff81 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10ff89 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x10ff89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10ff89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ff89 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10ff89 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x10ff89 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10ff8e [0x4C, 0x8B, 0x6C, 0x24, 0x38] (LoadPre 0x10ff8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10ff8e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff8e 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x10ff8e 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x10ff8e 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10ff93 [0x48, 0x8B, 0x6C, 0x24, 0x40] (LoadPre 0x10ff93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10ff93 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff93 5 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x10ff93 5 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x10ff93 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10ff98 [0x4C, 0x8B, 0x74, 0x24, 0x48] (LoadPre 0x10ff98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10ff98 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff98 14 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x10ff98 14 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10ff98 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10ff9d [0x4C, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x10ff9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10ff9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ff9d 15 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10ff9d 15 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10ff9d 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10ffa2 [0x4C, 0x8B, 0x64, 0x24, 0x58] (LoadPre 0x10ffa2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ffa2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffa2 12 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10ffa2 12 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10ffa2 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10ffa7 [0x8B, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x10ffa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10ffa7 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10ffa7 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x10ffa7 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r32_m32_low_effect_step 0x10ffa7 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10ffae [0xE8, 0x9D, 0x7D, 0x01, 0x00] (PushPre 0x10ffae 5) (callEffect (fun _ => 0x127d50) 0x10ffb3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10ffae 0x127d50 0x10ffb3).toInstrSpec (call_rel32_effect_step 0x10ffae 0x17d9d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff5e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff63) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff68) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff6d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff72) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff77) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff7c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff81) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff89) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff8e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff93) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff98) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (14, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ff9d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 68), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffa2) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 68), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffa7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 70), (6, 6), (7, 78), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 68), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffae) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 80), (5, 70), (6, 6), (7, 78), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 68), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f16 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 82) (by decide) (by decide) rfl rfl

theorem block_l10ff59 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ff59 :=
  Rest.liftedBlock (rest_l10ff59 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ff59 x hx)

theorem rest_l10ffb3_2 [Bindings] (code : CodeMap) :
    Rest (n := 117) code lifted (codeRange 0x10ffb3 bytes_l10ffb3) [(0, 114), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      9 0x110054 bytes_l10ffb3_2 b_l10ffb3_2 := by
  have f40 : InstrSpec 0x110054 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x110054) (movR64R64Effect 0x110054 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110054 0 3).toInstrSpec (mov_r64_r64_effect_step 0x110054 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x110057 [0x48, 0x81, 0xC4, 0x48, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x110057) (addR64Imm32Effect 0x110057 4 0x148)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x110057 4 0x148).toInstrSpec (add_r64_imm32_effect_step 0x110057 0x48 0xc4 0x148 (by decide) (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x11005e [0x5B] (PopPre 0x11005e) (popR64Effect 0x11005e 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11005e 1 3).toInstrSpec (pop_r64_effect_step 0x11005e 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f43 : InstrSpec 0x11005f [0x41, 0x5C] (PopPre 0x11005f) (popR64Effect 0x11005f 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11005f 2 12).toInstrSpec (pop_r64_rex_effect_step 0x11005f 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f44 : InstrSpec 0x110061 [0x41, 0x5D] (PopPre 0x110061) (popR64Effect 0x110061 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110061 2 13).toInstrSpec (pop_r64_rex_effect_step 0x110061 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f45 : InstrSpec 0x110063 [0x41, 0x5E] (PopPre 0x110063) (popR64Effect 0x110063 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110063 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110063 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f46 : InstrSpec 0x110065 [0x41, 0x5F] (PopPre 0x110065) (popR64Effect 0x110065 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110065 2 15).toInstrSpec (pop_r64_rex_effect_step 0x110065 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f47 : InstrSpec 0x110067 [0x5D] (PopPre 0x110067) (popR64Effect 0x110067 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110067 1 5).toInstrSpec (pop_r64_effect_step 0x110067 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f48 : InstrSpec 0x110068 [0xC3] (RetPre 0x110068) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x110068).toInstrSpec (ret_effect_step 0x110068) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f40 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110057) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f41 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 3), (4, 119), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11005e) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f42 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 122) f42 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 123) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 122), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11005f) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f43 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 125) f43 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 126) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 125), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110061) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f44 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 128) f44 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 129) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 128), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110063) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f45 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 131) f45 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 132) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 131), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 130), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110065) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f46 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 134) f46 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 135) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 134), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 130), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110067) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f47 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 137) f47 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 138) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 137), (5, 136), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 130), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110068) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f48 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 140) f48 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 141) (ρ' := [(0, 117), (1, 111), (2, 67), (3, 121), (4, 140), (5, 136), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 124), (13, 127), (14, 130), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) f48 (by decide) rfl rfl rfl (by decide)

theorem rest_l10ffb3_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x10ffb3 bytes_l10ffb3) [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]
      29 0x10fff8 bytes_l10ffb3_1 b_l10ffb3_1 := by
  have f20 : InstrSpec 0x10fff8 [0x48, 0x23, 0x44, 0x24, 0x30] (LoadPre 0x10fff8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10fff8 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x10fff8 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (andR64M64Effect_footprint 0x10fff8 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (and_r64_m64_effect_step 0x10fff8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x10fffd [0x48, 0xC7, 0x43, 0x58, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fffd 8 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x10fffd + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fffd (.base 3 (.d8 0x58)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fffd (.base 3 (.d8 0x58)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fffd 0x48 (by decide) (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x110005 [0x48, 0xC7, 0x43, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x110005 8 (fun s => AddrMode.addr (.base 3 (.d8 0x60)) s (0x110005 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x110005 (.base 3 (.d8 0x60)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x110005 (.base 3 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x110005 0x48 (by decide) (.base 3 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x11000d [0x48, 0xC7, 0x43, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11000d 8 (fun s => AddrMode.addr (.base 3 (.d8 0x68)) s (0x11000d + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x11000d (.base 3 (.d8 0x68)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11000d (.base 3 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11000d 0x48 (by decide) (.base 3 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x110015 [0x48, 0xC7, 0x43, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x110015 8 (fun s => AddrMode.addr (.base 3 (.d8 0x70)) s (0x110015 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x110015 (.base 3 (.d8 0x70)) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x110015 (.base 3 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x110015 0x48 (by decide) (.base 3 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x11001d [0x4C, 0x89, 0x2B] (StorePre 0x11001d 3 (fun s => AddrMode.addr (.base 3 .none) s (0x11001d + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11001d 13 (.base 3 .none))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11001d 13 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11001d 0x4c (by decide) 5 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x110020 [0x48, 0x89, 0x6B, 0x08] (StorePre 0x110020 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x110020 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110020 5 (.base 3 (.d8 0x8)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110020 5 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110020 0x48 (by decide) 5 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x110024 [0x4C, 0x89, 0x73, 0x10] (StorePre 0x110024 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x110024 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110024 14 (.base 3 (.d8 0x10)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110024 14 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x110024 0x4c (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x110028 [0x4C, 0x89, 0x7B, 0x18] (StorePre 0x110028 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x110028 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110028 15 (.base 3 (.d8 0x18)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110028 15 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x110028 0x4c (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x11002c [0x4C, 0x89, 0x63, 0x20] (StorePre 0x11002c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x11002c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11002c 12 (.base 3 (.d8 0x20)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11002c 12 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x11002c 0x4c (by decide) 4 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x110030 [0x48, 0x89, 0x53, 0x28] (StorePre 0x110030 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x110030 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110030 2 (.base 3 (.d8 0x28)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110030 2 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x110030 0x48 (by decide) 2 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x110034 [0x48, 0x89, 0x73, 0x30] (StorePre 0x110034 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x110034 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110034 6 (.base 3 (.d8 0x30)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110034 6 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x110034 0x48 (by decide) 6 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x110038 [0x48, 0x89, 0x7B, 0x38] (StorePre 0x110038 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x110038 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110038 7 (.base 3 (.d8 0x38)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110038 7 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x110038 0x48 (by decide) 7 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x11003c [0x4C, 0x89, 0x43, 0x40] (StorePre 0x11003c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x11003c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11003c 8 (.base 3 (.d8 0x40)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x11003c 8 (.base 3 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x11003c 0x4c (by decide) 0 (.base 3 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x110040 [0x48, 0x89, 0x43, 0x48] (StorePre 0x110040 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x110040 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110040 0 (.base 3 (.d8 0x48)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110040 0 (.base 3 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x110040 0x48 (by decide) 0 (.base 3 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x110044 [0xF7, 0xD1] (fun s => s.RIP = 0x110044) (notR32Effect 0x110044 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR32Effect_footprint 0x110044 2 1).toInstrSpec (not_r32_effect_step 0x110044 0xd1 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x110046 [0x83, 0xE1, 0x01] (fun s => s.RIP = 0x110046) (andR32Imm8Effect 0x110046 3 1 0x1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x110046 3 1 0x1).toInstrSpec (and_r32_imm8_effect_step 0x110046 0xe1 0x1 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x110049 [0x48, 0x89, 0x4B, 0x50] (StorePre 0x110049 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x110049 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110049 1 (.base 3 (.d8 0x50)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x110049 1 (.base 3 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x110049 0x48 (by decide) 1 (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f38 : InstrSpec 0x11004d [0x8B, 0x44, 0x24, 0x0C] (LoadPre 0x11004d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x11004d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11004d 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x11004d 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x11004d 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x110051 [0x88, 0x43, 0x78] (StorePre 0x110051 3 (fun s => AddrMode.addr (.base 3 (.d8 0x78)) s (0x110051 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110051 3 0 (.base 3 (.d8 0x78)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x110051 3 0 (.base 3 (.d8 0x78))).toInstrSpec (mov_m8_r8_effect_step 0x110051 0 (by decide) (.base 3 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fffd) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110005) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11000d) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110015) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11001d) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110020) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110024) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110028) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11002c) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.exec (n := 103) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110030) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110034) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110038) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11003c) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110040) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.exec (n := 108) (ρ' := [(0, 93), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110044) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f35 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 93), (1, 109), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110046) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 93), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110049) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 93), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11004d) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 114), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110051) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.exec (n := 116) (ρ' := [(0, 114), (1, 111), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110054) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10ffb3_2 code

theorem rest_l10ffb3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10ffb3 bytes_l10ffb3) (entryMap (live .l10ffb3))
      49 0x10ffb3 bytes_l10ffb3 b_l10ffb3 := by
  have f0 : InstrSpec 0x10ffb3 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x10ffb3) (movzxR32R8Effect 0x10ffb3 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x10ffb3 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x10ffb3 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10ffb6 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x10ffb6) (movR64R64Effect 0x10ffb6 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10ffb6 1 0).toInstrSpec (mov_r64_r64_effect_step 0x10ffb6 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10ffb9 [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x10ffb9) (negR64Effect 0x10ffb9 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x10ffb9 1).toInstrSpec (neg_r64_effect_step 0x10ffb9 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10ffbc [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x10ffbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ffbc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffbc 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10ffbc 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10ffbc 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10ffc1 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10ffc1) (movR64R64Effect 0x10ffc1 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10ffc1 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10ffc1 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10ffc4 [0x48, 0x83, 0xF2, 0x01] (fun s => s.RIP = 0x10ffc4) (xorR64Imm8Effect 0x10ffc4 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x10ffc4 2 0x1).toInstrSpec (xor_r64_imm8_effect_step 0x10ffc4 0x48 0xf2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10ffc8 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x10ffc8) (andR64R64Effect 0x10ffc8 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffc8 2 1).toInstrSpec (and_r64_r64_effect_step 0x10ffc8 0x48 0xca (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10ffcb [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x10ffcb) (xorR64R64Effect 0x10ffcb 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x10ffcb 2 6).toInstrSpec (xor_r64_r64_effect_step 0x10ffcb 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10ffce [0x48, 0xFF, 0xC8] (fun s => s.RIP = 0x10ffce) (decR64Effect 0x10ffce 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (decR64Effect_footprint 0x10ffce 0).toInstrSpec (dec_r64_effect_step 0x10ffce 0x48 0xc8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10ffd1 [0x49, 0x21, 0xC5] (fun s => s.RIP = 0x10ffd1) (andR64R64Effect 0x10ffd1 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffd1 13 0).toInstrSpec (and_r64_r64_effect_step 0x10ffd1 0x49 0xc5 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10ffd4 [0x48, 0x21, 0xC5] (fun s => s.RIP = 0x10ffd4) (andR64R64Effect 0x10ffd4 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffd4 5 0).toInstrSpec (and_r64_r64_effect_step 0x10ffd4 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10ffd7 [0x49, 0x21, 0xC6] (fun s => s.RIP = 0x10ffd7) (andR64R64Effect 0x10ffd7 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffd7 14 0).toInstrSpec (and_r64_r64_effect_step 0x10ffd7 0x49 0xc6 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10ffda [0x49, 0x21, 0xC7] (fun s => s.RIP = 0x10ffda) (andR64R64Effect 0x10ffda 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffda 15 0).toInstrSpec (and_r64_r64_effect_step 0x10ffda 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10ffdd [0x49, 0x21, 0xC4] (fun s => s.RIP = 0x10ffdd) (andR64R64Effect 0x10ffdd 12 0)
      [.gpr 12, .gpr 0] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffdd 12 0).toInstrSpec (and_r64_r64_effect_step 0x10ffdd 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10ffe0 [0x48, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x10ffe0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ffe0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffe0 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10ffe0 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x10ffe0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10ffe5 [0x48, 0x21, 0xC6] (fun s => s.RIP = 0x10ffe5) (andR64R64Effect 0x10ffe5 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffe5 6 0).toInstrSpec (and_r64_r64_effect_step 0x10ffe5 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10ffe8 [0x48, 0x8B, 0x7C, 0x24, 0x20] (LoadPre 0x10ffe8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ffe8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ffe8 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10ffe8 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x10ffe8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10ffed [0x48, 0x21, 0xC7] (fun s => s.RIP = 0x10ffed) (andR64R64Effect 0x10ffed 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10ffed 7 0).toInstrSpec (and_r64_r64_effect_step 0x10ffed 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10fff0 [0x4C, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x10fff0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10fff0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fff0 8 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x10fff0 8 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x10fff0 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10fff5 [0x49, 0x21, 0xC0] (fun s => s.RIP = 0x10fff5) (andR64R64Effect 0x10fff5 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x10fff5 8 0).toInstrSpec (and_r64_r64_effect_step 0x10fff5 0x49 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffb6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffb9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffbc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffc1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffc4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 63), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffc8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 57), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffcb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 57), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffce) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffd1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffd4) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffd7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 75), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffda) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffdd) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 59), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffe0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 81), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffe5) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffe8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 85), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ffed) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fff0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 89), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fff5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 69), (1, 57), (2, 67), (3, 3), (4, 4), (5, 73), (6, 83), (7, 87), (8, 91), (9, 9), (10, 10), (11, 11), (12, 79), (13, 71), (14, 75), (15, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fff8) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10ffb3_1 code

theorem block_l10ffb3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10ffb3 :=
  Rest.liftedBlock (rest_l10ffb3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10ffb3 x hx)

theorem rest_l110070 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110070 bytes_l110070) (entryMap (live .l110070))
      7 0x110070 bytes_l110070 b_l110070 := by
  have f0 : InstrSpec 0x110070 [0x41, 0x56] (PushPre 0x110070 2) (pushR64Effect 0x110070 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110070 2 14).toInstrSpec (push_r64_rex_effect_step 0x110070 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x110072 [0x53] (PushPre 0x110072 1) (pushR64Effect 0x110072 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110072 1 3).toInstrSpec (push_r64_effect_step 0x110072 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x110073 [0x48, 0x83, 0xEC, 0x58] (fun s => s.RIP = 0x110073) (subR64Imm8Effect 0x110073 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x110073 4 0x58).toInstrSpec (sub_r64_imm8_effect_step 0x110073 0x48 0xec 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x110077 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x110077) (movR64R64Effect 0x110077 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x110077 3 7).toInstrSpec (mov_r64_r64_effect_step 0x110077 0x48 0xfb (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11007a [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x11007a) (movR64R64Effect 0x11007a 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11007a 14 4).toInstrSpec (mov_r64_r64_effect_step 0x11007a 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11007d [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11007d) (movR64R64Effect 0x11007d 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11007d 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11007d 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x110080 [0xE8, 0x5B, 0xEC, 0xFF, 0xFF] (PushPre 0x110080 5) (callEffect (fun _ => 0x10ece0) 0x110085)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x110080 0x10ece0 0x110085).toInstrSpec (call_rel32_effect_step 0x110080 0xffffec5b (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110072) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110073) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110077) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11007a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11007d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 59), (4, 57), (5, 5), (6, 6), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110080) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 59), (4, 65), (5, 5), (6, 6), (7, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10ece0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l110070 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110070 :=
  Rest.liftedBlock (rest_l110070 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110070 x hx)

theorem rest_l110085 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110085 bytes_l110085) (entryMap (live .l110085))
      3 0x110085 bytes_l110085 b_l110085 := by
  have f0 : InstrSpec 0x110085 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x110085) (movR64R64Effect 0x110085 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x110085 7 3).toInstrSpec (mov_r64_r64_effect_step 0x110085 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110088 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x110088) (movR64R64Effect 0x110088 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x110088 6 14).toInstrSpec (mov_r64_r64_effect_step 0x110088 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11008b [0xE8, 0x20, 0x11, 0x01, 0x00] (PushPre 0x11008b 5) (callEffect (fun _ => 0x1211b0) 0x110090)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11008b 0x1211b0 0x110090).toInstrSpec (call_rel32_effect_step 0x11008b 0x11120 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110088) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11008b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211b0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l110085 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110085 :=
  Rest.liftedBlock (rest_l110085 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110085 x hx)

theorem rest_l110090 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110090 bytes_l110090) (entryMap (live .l110090))
      5 0x110090 bytes_l110090 b_l110090 := by
  have f0 : InstrSpec 0x110090 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x110090) (movR64R64Effect 0x110090 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110090 0 3).toInstrSpec (mov_r64_r64_effect_step 0x110090 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x110093 [0x48, 0x83, 0xC4, 0x58] (fun s => s.RIP = 0x110093) (addR64Imm8Effect 0x110093 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x110093 4 0x58).toInstrSpec (add_r64_imm8_effect_step 0x110093 0x48 0xc4 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x110097 [0x5B] (PopPre 0x110097) (popR64Effect 0x110097 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110097 1 3).toInstrSpec (pop_r64_effect_step 0x110097 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x110098 [0x41, 0x5E] (PopPre 0x110098) (popR64Effect 0x110098 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110098 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110098 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x11009a [0xC3] (RetPre 0x11009a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11009a).toInstrSpec (ret_effect_step 0x11009a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110093) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110097) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110098) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11009a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l110090 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110090 :=
  Rest.liftedBlock (rest_l110090 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110090 x hx)

theorem rest_l110b80_4 [Bindings] (code : CodeMap) :
    Rest (n := 204) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x110c99 bytes_l110b80_4 b_l110b80_4 := by
  have f80 : InstrSpec 0x110c99 [0x49, 0xFF, 0xCA] (fun s => s.RIP = 0x110c99) (decR64Effect 0x110c99 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (decR64Effect_footprint 0x110c99 10).toInstrSpec (dec_r64_effect_step 0x110c99 0x49 0xca (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x110c9c [0x4D, 0x21, 0xC2] (fun s => s.RIP = 0x110c9c) (andR64R64Effect 0x110c9c 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c9c 10 8).toInstrSpec (and_r64_r64_effect_step 0x110c9c 0x4d 0xc2 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x110c9f [0x49, 0xFF, 0xCB] (fun s => s.RIP = 0x110c9f) (decR64Effect 0x110c9f 11)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (decR64Effect_footprint 0x110c9f 11).toInstrSpec (dec_r64_effect_step 0x110c9f 0x49 0xcb (by decide) (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x110ca2 [0x49, 0x21, 0xDB] (fun s => s.RIP = 0x110ca2) (andR64R64Effect 0x110ca2 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110ca2 11 3).toInstrSpec (and_r64_r64_effect_step 0x110ca2 0x49 0xdb (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x110ca5 [0x0F, 0xB6, 0x4C, 0x24, 0x07] (LoadPre 0x110ca5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110ca5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x110ca5 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f85 : InstrSpec 0x110caa [0x48, 0xFF, 0xC9] (fun s => s.RIP = 0x110caa) (decR64Effect 0x110caa 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (decR64Effect_footprint 0x110caa 1).toInstrSpec (dec_r64_effect_step 0x110caa 0x48 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x110cad [0x48, 0x21, 0xF1] (fun s => s.RIP = 0x110cad) (andR64R64Effect 0x110cad 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110cad 1 6).toInstrSpec (and_r64_r64_effect_step 0x110cad 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x110cb0 [0x48, 0x89, 0x17] (StorePre 0x110cb0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x110cb0 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110cb0 2 (.base 7 .none))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cb0 2 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x110cb0 0x48 (by decide) 2 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f88 : InstrSpec 0x110cb3 [0x4C, 0x89, 0x57, 0x08] (StorePre 0x110cb3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x110cb3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb3 10 (.base 7 (.d8 0x8)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cb3 10 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110cb3 0x4c (by decide) 2 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f89 : InstrSpec 0x110cb7 [0x4C, 0x89, 0x5F, 0x10] (StorePre 0x110cb7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x110cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb7 11 (.base 7 (.d8 0x10)))
      [.gpr 11, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cb7 11 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x110cb7 0x4c (by decide) 3 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f90 : InstrSpec 0x110cbb [0x48, 0x89, 0x4F, 0x18] (StorePre 0x110cbb 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x110cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cbb 1 (.base 7 (.d8 0x18)))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x110cbb 1 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x110cbb 0x48 (by decide) 1 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f91 : InstrSpec 0x110cbf [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x110cbf) (addR64Imm8Effect 0x110cbf 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x110cbf 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x110cbf 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x110cc3 [0x5B] (PopPre 0x110cc3) (popR64Effect 0x110cc3 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc3 1 3).toInstrSpec (pop_r64_effect_step 0x110cc3 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f93 : InstrSpec 0x110cc4 [0x41, 0x5C] (PopPre 0x110cc4) (popR64Effect 0x110cc4 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc4 2 12).toInstrSpec (pop_r64_rex_effect_step 0x110cc4 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f94 : InstrSpec 0x110cc6 [0x41, 0x5E] (PopPre 0x110cc6) (popR64Effect 0x110cc6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x110cc6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f95 : InstrSpec 0x110cc8 [0x41, 0x5F] (PopPre 0x110cc8) (popR64Effect 0x110cc8 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x110cc8 2 15).toInstrSpec (pop_r64_rex_effect_step 0x110cc8 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f96 : InstrSpec 0x110cca [0xC3] (RetPre 0x110cca) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x110cca).toInstrSpec (ret_effect_step 0x110cca) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f80 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 204), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c9c) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f81 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c9f) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f82 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 208), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ca2) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f83 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ca5) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 198), (1, 212), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110caa) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f85 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 198), (1, 214), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cad) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f86 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cb0) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.exec (n := 218) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cb3) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 219) (RestInside.exec (n := 219) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cb7) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 220) (RestInside.exec (n := 220) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cbb) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 221) (RestInside.exec (n := 221) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cbf) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f91 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 136), (4, 222), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc3) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f92 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 225) f92 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 226) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 225), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc4) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f93 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 228) f93 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 229) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 228), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc6) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f94 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 231) f94 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 232) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 231), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cc8) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f95 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 234) f95 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 235) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 234), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110cca) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f96 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 237) f96 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 238) (ρ' := [(0, 198), (1, 216), (2, 202), (3, 224), (4, 237), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)]) f96 (by decide) rfl rfl rfl (by decide)

theorem rest_l110b80_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 167), (22, 22), (39, 39), (50, 50), (51, 51)]
      37 0x110c48 bytes_l110b80_3 b_l110b80_3 := by
  have f60 : InstrSpec 0x110c48 [0x49, 0x21, 0xD7] (fun s => s.RIP = 0x110c48) (andR64R64Effect 0x110c48 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c48 15 2).toInstrSpec (and_r64_r64_effect_step 0x110c48 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x110c4b [0x4C, 0x09, 0xCA] (fun s => s.RIP = 0x110c4b) (orR64R64Effect 0x110c4b 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c4b 2 9).toInstrSpec (or_r64_r64_effect_step 0x110c4b 0x4c 0xca (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x110c4e [0x48, 0x21, 0xF2] (fun s => s.RIP = 0x110c4e) (andR64R64Effect 0x110c4e 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c4e 2 6).toInstrSpec (and_r64_r64_effect_step 0x110c4e 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x110c51 [0x4C, 0x09, 0xFA] (fun s => s.RIP = 0x110c51) (orR64R64Effect 0x110c51 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c51 2 15).toInstrSpec (or_r64_r64_effect_step 0x110c51 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x110c54 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x110c54) (shrR64Effect 0x110c54 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x110c54 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x110c54 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x110c58 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x110c58 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c58 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c58 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110c58 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110c58 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x110c5d [0x4C, 0x09, 0xD0] (fun s => s.RIP = 0x110c5d) (orR64R64Effect 0x110c5d 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c5d 0 10).toInstrSpec (or_r64_r64_effect_step 0x110c5d 0x4c 0xd0 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x110c60 [0x4C, 0x09, 0xD8] (fun s => s.RIP = 0x110c60) (orR64R64Effect 0x110c60 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c60 0 11).toInstrSpec (or_r64_r64_effect_step 0x110c60 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x110c63 [0x4C, 0x09, 0xC8] (fun s => s.RIP = 0x110c63) (orR64R64Effect 0x110c63 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c63 0 9).toInstrSpec (or_r64_r64_effect_step 0x110c63 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x110c66 [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c66 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c66 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c66 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c66 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c66 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x110c6b [0x4C, 0x8D, 0x4C, 0x24, 0x07] (fun s => s.RIP = 0x110c6b) (leaR64Effect 0x110c6b 9 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (leaR64Effect_footprint 0x110c6b 9 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x110c6b 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x110c70 [0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x110c70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c70 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x110c70 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x110c75 [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c75 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c75 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c75 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c75 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x110c7a [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x110c7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c7a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x110c7a 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f74 : InstrSpec 0x110c80 [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c80 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c80 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c80 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c80 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x110c85 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x07] (LoadPre 0x110c85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c85 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x110c85 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x110c8b [0x0F, 0x94, 0x44, 0x24, 0x07] (StorePre 0x110c8b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c8b + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c8b 5 (.sib 4 none 0 (.d8 0x7))))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF] [.rip] :=
    (setccM8Effect_footprint 0x110c8b 5 (.sib 4 none 0 (.d8 0x7)) 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_m8_effect_step 0x110c8b 4 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide) c)) (StorePre.of_addr rfl)
  have f77 : InstrSpec 0x110c90 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x110c90) (movR64R64Effect 0x110c90 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x110c90 0 7).toInstrSpec (mov_r64_r64_effect_step 0x110c90 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x110c93 [0x48, 0xFF, 0xCA] (fun s => s.RIP = 0x110c93) (decR64Effect 0x110c93 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (decR64Effect_footprint 0x110c93 2).toInstrSpec (dec_r64_effect_step 0x110c93 0x48 0xca (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x110c96 [0x48, 0x21, 0xCA] (fun s => s.RIP = 0x110c96) (andR64R64Effect 0x110c96 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c96 2 1).toInstrSpec (and_r64_r64_effect_step 0x110c96 0x48 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c4b) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 65), (1, 75), (2, 171), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c4e) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 65), (1, 75), (2, 173), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c51) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 65), (1, 75), (2, 175), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c54) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 65), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c58) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.exec (n := 179) (ρ' := [(0, 65), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c5d) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f66 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 180), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c60) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f67 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 182), (1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c63) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f68 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c66) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c6b) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f70 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(1, 75), (2, 177), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c70) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f71 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c75) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.exec (n := 191) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 63), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c7a) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f73 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c80) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.exec (n := 194) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 67), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c85) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f75 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c8b) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.exec (n := 197) (ρ' := [(1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c90) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f77 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 198), (1, 75), (2, 189), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (19, 184), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c93) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f78 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 198), (1, 75), (2, 200), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c96) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f79 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 198), (1, 75), (2, 202), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 192), (11, 195), (12, 142), (13, 13), (15, 169), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c99) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110b80_4 code

theorem rest_l110b80_2 [Bindings] (code : CodeMap) :
    Rest (n := 130) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]
      57 0x110c04 bytes_l110b80_2 b_l110b80_2 := by
  have f40 : InstrSpec 0x110c04 [0x4D, 0x89, 0xFC] (fun s => s.RIP = 0x110c04) (movR64R64Effect 0x110c04 12 15)
      [.gpr 15] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x110c04 12 15).toInstrSpec (mov_r64_r64_effect_step 0x110c04 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x110c07 [0x4D, 0x29, 0xDC] (fun s => s.RIP = 0x110c07) (subR64R64Effect 0x110c07 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110c07 12 11).toInstrSpec (sub_r64_r64_effect_step 0x110c07 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x110c0a [0x48, 0xC1, 0xFB, 0x3F] (fun s => s.RIP = 0x110c0a) (sarR64Effect 0x110c0a 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (sarR64Effect_footprint 0x110c0a 4 3 63).toInstrSpec (sar_r64_imm8_effect_step 0x110c0a 0x48 0xfb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x110c0e [0x4C, 0x01, 0xE3] (fun s => s.RIP = 0x110c0e) (addR64R64Effect 0x110c0e 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110c0e 3 12).toInstrSpec (add_r64_r64_effect_step 0x110c0e 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x110c11 [0x49, 0xF7, 0xD7] (fun s => s.RIP = 0x110c11) (notR64Effect 0x110c11 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR64Effect_footprint 0x110c11 15).toInstrSpec (not_r64_effect_step 0x110c11 0x49 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x110c14 [0x4D, 0x89, 0xDC] (fun s => s.RIP = 0x110c14) (movR64R64Effect 0x110c14 12 11)
      [.gpr 11] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x110c14 12 11).toInstrSpec (mov_r64_r64_effect_step 0x110c14 0x4d 0xdc (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x110c17 [0x4D, 0x21, 0xFC] (fun s => s.RIP = 0x110c17) (andR64R64Effect 0x110c17 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c17 12 15).toInstrSpec (and_r64_r64_effect_step 0x110c17 0x4d 0xfc (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x110c1a [0x4D, 0x09, 0xDF] (fun s => s.RIP = 0x110c1a) (orR64R64Effect 0x110c1a 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c1a 15 11).toInstrSpec (or_r64_r64_effect_step 0x110c1a 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x110c1d [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x110c1d) (andR64R64Effect 0x110c1d 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110c1d 15 3).toInstrSpec (and_r64_r64_effect_step 0x110c1d 0x49 0xdf (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x110c20 [0x4D, 0x09, 0xE7] (fun s => s.RIP = 0x110c20) (orR64R64Effect 0x110c20 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110c20 15 12).toInstrSpec (or_r64_r64_effect_step 0x110c20 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x110c23 [0x49, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x110c23) (shrR64Effect 0x110c23 4 15 63)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR64Effect_footprint 0x110c23 4 15 63).toInstrSpec (shr_r64_imm8_effect_step 0x110c23 0x49 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x110c27 [0x4C, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x110c27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c27 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c27 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110c27 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110c27 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x110c2c [0x48, 0x2B, 0x74, 0x24, 0x08] (LoadPre 0x110c2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c2c + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110c2c 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110c2c 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x110c2c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f53 : InstrSpec 0x110c31 [0x48, 0x8B, 0x52, 0x18] (LoadPre 0x110c31 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x110c31 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c31 2 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x110c31 2 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x110c31 0x48 (by decide) 2 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x110c35 [0x49, 0x89, 0xD7] (fun s => s.RIP = 0x110c35) (movR64R64Effect 0x110c35 15 2)
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110c35 15 2).toInstrSpec (mov_r64_r64_effect_step 0x110c35 0x49 0xd7 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x110c38 [0x4D, 0x29, 0xCF] (fun s => s.RIP = 0x110c38) (subR64R64Effect 0x110c38 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110c38 15 9).toInstrSpec (sub_r64_r64_effect_step 0x110c38 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x110c3b [0x48, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x110c3b) (sarR64Effect 0x110c3b 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (sarR64Effect_footprint 0x110c3b 4 6 63).toInstrSpec (sar_r64_imm8_effect_step 0x110c3b 0x48 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x110c3f [0x4C, 0x01, 0xFE] (fun s => s.RIP = 0x110c3f) (addR64R64Effect 0x110c3f 6 15)
      [.gpr 6, .gpr 15] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110c3f 6 15).toInstrSpec (add_r64_r64_effect_step 0x110c3f 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x110c42 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x110c42) (notR64Effect 0x110c42 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x110c42 2).toInstrSpec (not_r64_effect_step 0x110c42 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x110c45 [0x4D, 0x89, 0xCF] (fun s => s.RIP = 0x110c45) (movR64R64Effect 0x110c45 15 9)
      [.gpr 9] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110c45 15 9).toInstrSpec (mov_r64_r64_effect_step 0x110c45 0x4d 0xcf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f40 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 130), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c07) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f41 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c0a) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f42 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 134), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c0e) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f43 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c11) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 132), (13, 13), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c14) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f45 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 140), (13, 13), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c17) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f46 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c1a) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f47 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 144), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c1d) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f48 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c20) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f49 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 148), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c23) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c27) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.exec (n := 152) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c2c) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c31) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 150), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c35) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 157), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c38) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 153), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c3b) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 161), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c3f) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 65), (1, 75), (2, 155), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c42) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 159), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c45) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 65), (1, 75), (2, 165), (3, 136), (4, 61), (5, 5), (6, 163), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 142), (13, 13), (15, 167), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c48) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110b80_3 code

theorem rest_l110b80_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x110b80 bytes_l110b80) [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      77 0x110bbe bytes_l110b80_1 b_l110b80_1 := by
  have f20 : InstrSpec 0x110bbe [0x4C, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x110bbe) (leaR64Effect 0x110bbe 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x110bbe 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x110bbe 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x110bc3 [0x31, 0xF6] (fun s => s.RIP = 0x110bc3) (xorR32R32Effect 0x110bc3 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110bc3 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x110bc3 0xf6 (by decide)) pre_rip
  have f22 : InstrSpec 0x110bc5 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x110bc5) (xorR32R32Effect 0x110bc5 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110bc5 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x110bc5 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x110bc8 [0x4C, 0x2B, 0x44, 0x24, 0x08] (LoadPre 0x110bc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bc8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bc8 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110bc8 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x110bc8 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x110bcd [0x48, 0x8B, 0x5A, 0x08] (LoadPre 0x110bcd (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x110bcd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110bcd 3 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x110bcd 3 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x110bcd 0x48 (by decide) 3 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x110bd1 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x110bd1) (movR64R64Effect 0x110bd1 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110bd1 15 3).toInstrSpec (mov_r64_r64_effect_step 0x110bd1 0x49 0xdf (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x110bd4 [0x49, 0x29, 0xC7] (fun s => s.RIP = 0x110bd4) (subR64R64Effect 0x110bd4 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110bd4 15 0).toInstrSpec (sub_r64_r64_effect_step 0x110bd4 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x110bd7 [0x49, 0xC1, 0xF8, 0x3F] (fun s => s.RIP = 0x110bd7) (sarR64Effect 0x110bd7 4 8 63)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (sarR64Effect_footprint 0x110bd7 4 8 63).toInstrSpec (sar_r64_imm8_effect_step 0x110bd7 0x49 0xf8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x110bdb [0x4D, 0x01, 0xF8] (fun s => s.RIP = 0x110bdb) (addR64R64Effect 0x110bdb 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x110bdb 8 15).toInstrSpec (add_r64_r64_effect_step 0x110bdb 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x110bde [0x48, 0xF7, 0xD3] (fun s => s.RIP = 0x110bde) (notR64Effect 0x110bde 3)
      [.gpr 3] [] [.reg 3, .rip] :=
    (notR64Effect_footprint 0x110bde 3).toInstrSpec (not_r64_effect_step 0x110bde 0x48 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x110be1 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x110be1) (movR64R64Effect 0x110be1 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x110be1 15 0).toInstrSpec (mov_r64_r64_effect_step 0x110be1 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x110be4 [0x49, 0x21, 0xDF] (fun s => s.RIP = 0x110be4) (andR64R64Effect 0x110be4 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110be4 15 3).toInstrSpec (and_r64_r64_effect_step 0x110be4 0x49 0xdf (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x110be7 [0x48, 0x09, 0xC3] (fun s => s.RIP = 0x110be7) (orR64R64Effect 0x110be7 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110be7 3 0).toInstrSpec (or_r64_r64_effect_step 0x110be7 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x110bea [0x4C, 0x21, 0xC3] (fun s => s.RIP = 0x110bea) (andR64R64Effect 0x110bea 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110bea 3 8).toInstrSpec (and_r64_r64_effect_step 0x110bea 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x110bed [0x4C, 0x09, 0xFB] (fun s => s.RIP = 0x110bed) (orR64R64Effect 0x110bed 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110bed 3 15).toInstrSpec (or_r64_r64_effect_step 0x110bed 0x4c 0xfb (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x110bf0 [0x48, 0xC1, 0xEB, 0x3F] (fun s => s.RIP = 0x110bf0) (shrR64Effect 0x110bf0 4 3 63)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR64Effect_footprint 0x110bf0 4 3 63).toInstrSpec (shr_r64_imm8_effect_step 0x110bf0 0x48 0xeb 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x110bf4 [0x48, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x110bf4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bf4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bf4 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110bf4 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110bf4 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x110bf9 [0x31, 0xDB] (fun s => s.RIP = 0x110bf9) (xorR32R32Effect 0x110bf9 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x110bf9 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x110bf9 0xdb (by decide)) pre_rip
  have f38 : InstrSpec 0x110bfb [0x48, 0x2B, 0x5C, 0x24, 0x08] (LoadPre 0x110bfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bfb + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bfb 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (subR64M64Effect_footprint 0x110bfb 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x110bfb 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x110c00 [0x4C, 0x8B, 0x7A, 0x10] (LoadPre 0x110c00 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x110c00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c00 15 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x110c00 15 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110c00 0x4c (by decide) 7 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bc3) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 93), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bc5) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 93), (7, 7), (8, 95), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bc8) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bcd) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bd1) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f25 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bd4) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 97), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bd7) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f27 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 105), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bdb) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f28 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 99), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bde) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f29 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 109), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 103), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110be1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f30 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 109), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110be4) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f31 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 109), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110be7) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 115), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bea) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 117), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bed) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 119), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bf0) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 121), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bf4) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.exec (n := 123) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 121), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bf9) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f37 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 124), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bfb) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f38 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 113), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c00) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f39 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 126), (4, 61), (5, 5), (6, 93), (7, 7), (8, 107), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (15, 128), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110c04) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l110b80_2 code

theorem rest_l110b80 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x110b80 bytes_l110b80) (entryMap (live .l110b80))
      97 0x110b80 bytes_l110b80 b_l110b80 := by
  have f0 : InstrSpec 0x110b80 [0x41, 0x57] (PushPre 0x110b80 2) (pushR64Effect 0x110b80 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b80 2 15).toInstrSpec (push_r64_rex_effect_step 0x110b80 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x110b82 [0x41, 0x56] (PushPre 0x110b82 2) (pushR64Effect 0x110b82 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b82 2 14).toInstrSpec (push_r64_rex_effect_step 0x110b82 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x110b84 [0x41, 0x54] (PushPre 0x110b84 2) (pushR64Effect 0x110b84 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b84 2 12).toInstrSpec (push_r64_rex_effect_step 0x110b84 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x110b86 [0x53] (PushPre 0x110b86 1) (pushR64Effect 0x110b86 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x110b86 1 3).toInstrSpec (push_r64_effect_step 0x110b86 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x110b87 [0x48, 0x83, 0xEC, 0x10] (fun s => s.RIP = 0x110b87) (subR64Imm8Effect 0x110b87 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x110b87 4 0x10).toInstrSpec (sub_r64_imm8_effect_step 0x110b87 0x48 0xec 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x110b8b [0x4C, 0x8B, 0x16] (LoadPre 0x110b8b (fun s => AddrMode.addr (.base 6 .none) s (0x110b8b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b8b 10 (.base 6 .none))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x110b8b 10 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110b8b 0x4c (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x110b8e [0x48, 0x8B, 0x46, 0x08] (LoadPre 0x110b8e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x110b8e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b8e 0 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x110b8e 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x110b8e 0x48 (by decide) 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x110b92 [0x4C, 0x8B, 0x5E, 0x10] (LoadPre 0x110b92 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x110b92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b92 11 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x110b92 11 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x110b92 0x4c (by decide) 3 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x110b96 [0x4C, 0x8B, 0x4E, 0x18] (LoadPre 0x110b96 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x110b96 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b96 9 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x110b96 9 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x110b96 0x4c (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x110b9a [0x48, 0x8B, 0x32] (LoadPre 0x110b9a (fun s => AddrMode.addr (.base 2 .none) s (0x110b9a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b9a 6 (.base 2 .none))
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x110b9a 6 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x110b9a 0x48 (by decide) 6 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x110b9d [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x110b9d) (movR64R64Effect 0x110b9d 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x110b9d 1 6).toInstrSpec (mov_r64_r64_effect_step 0x110b9d 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x110ba0 [0x4C, 0x29, 0xD1] (fun s => s.RIP = 0x110ba0) (subR64R64Effect 0x110ba0 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (subR64R64Effect_footprint 0x110ba0 1 10).toInstrSpec (sub_r64_r64_effect_step 0x110ba0 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x110ba3 [0x48, 0xF7, 0xD6] (fun s => s.RIP = 0x110ba3) (notR64Effect 0x110ba3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR64Effect_footprint 0x110ba3 6).toInstrSpec (not_r64_effect_step 0x110ba3 0x48 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x110ba6 [0x4D, 0x89, 0xD0] (fun s => s.RIP = 0x110ba6) (movR64R64Effect 0x110ba6 8 10)
      [.gpr 10] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x110ba6 8 10).toInstrSpec (mov_r64_r64_effect_step 0x110ba6 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x110ba9 [0x49, 0x21, 0xF0] (fun s => s.RIP = 0x110ba9) (andR64R64Effect 0x110ba9 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110ba9 8 6).toInstrSpec (and_r64_r64_effect_step 0x110ba9 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x110bac [0x4C, 0x09, 0xD6] (fun s => s.RIP = 0x110bac) (orR64R64Effect 0x110bac 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110bac 6 10).toInstrSpec (or_r64_r64_effect_step 0x110bac 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x110baf [0x48, 0x21, 0xCE] (fun s => s.RIP = 0x110baf) (andR64R64Effect 0x110baf 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x110baf 6 1).toInstrSpec (and_r64_r64_effect_step 0x110baf 0x48 0xce (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x110bb2 [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x110bb2) (orR64R64Effect 0x110bb2 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x110bb2 6 8).toInstrSpec (or_r64_r64_effect_step 0x110bb2 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x110bb5 [0x48, 0xC1, 0xEE, 0x3F] (fun s => s.RIP = 0x110bb5) (shrR64Effect 0x110bb5 4 6 63)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x110bb5 4 6 63).toInstrSpec (shr_r64_imm8_effect_step 0x110bb5 0x48 0xee 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x110bb9 [0x48, 0x89, 0x74, 0x24, 0x08] (StorePre 0x110bb9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bb9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bb9 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x110bb9 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x110bb9 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b82) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b84) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b86) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b87) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b8b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b8e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b92) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b96) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b9a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (2, 2), (3, 3), (4, 61), (5, 5), (6, 71), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110b9d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 65), (1, 73), (2, 2), (3, 3), (4, 61), (5, 5), (6, 71), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 71), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 77), (7, 7), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 77), (7, 7), (8, 79), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110ba9) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 77), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bac) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 83), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110baf) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 85), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bb2) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 87), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bb5) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bb9) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 65), (1, 75), (2, 2), (3, 3), (4, 61), (5, 5), (6, 89), (7, 7), (8, 81), (9, 69), (10, 63), (11, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x110bbe) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l110b80_1 code

theorem block_l110b80 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l110b80 :=
  Rest.liftedBlock (rest_l110b80 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l110b80 x hx)

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

theorem rest_l120350 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120350 bytes_l120350) (entryMap (live .l120350))
      18 0x120350 bytes_l120350 b_l120350 := by
  have f0 : InstrSpec 0x120350 [0x41, 0x56] (PushPre 0x120350 2) (pushR64Effect 0x120350 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120350 2 14).toInstrSpec (push_r64_rex_effect_step 0x120350 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x120352 [0x53] (PushPre 0x120352 1) (pushR64Effect 0x120352 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120352 1 3).toInstrSpec (push_r64_effect_step 0x120352 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x120353 [0x48, 0x83, 0xEC, 0x58] (fun s => s.RIP = 0x120353) (subR64Imm8Effect 0x120353 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x120353 4 0x58).toInstrSpec (sub_r64_imm8_effect_step 0x120353 0x48 0xec 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x120357 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x120357) (movR64R64Effect 0x120357 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x120357 3 7).toInstrSpec (mov_r64_r64_effect_step 0x120357 0x48 0xfb (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12035a [0x48, 0x8B, 0x46, 0x20] (LoadPre 0x12035a (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x12035a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12035a 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12035a 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x12035a 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x12035e [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x12035e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12035e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12035e 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12035e 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x12035e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x120363 [0x48, 0x8B, 0x46, 0x18] (LoadPre 0x120363 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x120363 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120363 0 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120363 0 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x120363 0x48 (by decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x120367 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x120367 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x120367 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120367 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120367 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x120367 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x12036c [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x12036c (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x12036c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12036c 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12036c 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12036c 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x120370 [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x120370 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x120370 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120370 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120370 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x120370 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x120375 [0x48, 0x8B, 0x06] (LoadPre 0x120375 (fun s => AddrMode.addr (.base 6 .none) s (0x120375 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x120375 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120375 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x120375 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x120378 [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x120378 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x120378 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120378 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120378 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x120378 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12037c [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x12037c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12037c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12037c 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12037c 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12037c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x120381 [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x120381 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120381 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120381 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120381 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x120381 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x120386 [0x4C, 0x8D, 0x74, 0x24, 0x30] (fun s => s.RIP = 0x120386) (leaR64Effect 0x120386 14 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x120386 14 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x120386 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x12038b [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x12038b) (leaR64Effect 0x12038b 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x12038b 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x12038b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x120390 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x120390) (movR64R64Effect 0x120390 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x120390 7 14).toInstrSpec (mov_r64_r64_effect_step 0x120390 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x120393 [0xE8, 0x98, 0x45, 0xFF, 0xFF] (PushPre 0x120393 5) (callEffect (fun _ => 0x114930) 0x120398)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x120393 0x114930 0x120398).toInstrSpec (call_rel32_effect_step 0x120393 0xffff4598 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120352) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120353) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120357) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12035a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12035e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120363) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120367) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12036c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120370) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120375) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120378) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12037c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120381) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120386) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12038b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 78), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120390) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 57), (5, 5), (6, 78), (7, 80), (10, 10), (11, 11), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120393) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 70), (1, 72), (3, 59), (4, 82), (5, 5), (6, 78), (7, 80), (10, 10), (11, 11), (12, 12), (13, 13), (14, 76), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x114930) f17 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 84) (by decide) (by decide) rfl rfl

theorem block_l120350 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120350 :=
  Rest.liftedBlock (rest_l120350 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120350 x hx)

theorem rest_l120398 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120398 bytes_l120398) (entryMap (live .l120398))
      3 0x120398 bytes_l120398 b_l120398 := by
  have f0 : InstrSpec 0x120398 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x120398) (movR64R64Effect 0x120398 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x120398 7 3).toInstrSpec (mov_r64_r64_effect_step 0x120398 0x48 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12039b [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x12039b) (movR64R64Effect 0x12039b 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12039b 6 14).toInstrSpec (mov_r64_r64_effect_step 0x12039b 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12039e [0xE8, 0x2D, 0x45, 0xFF, 0xFF] (PushPre 0x12039e 5) (callEffect (fun _ => 0x1148d0) 0x1203a3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x12039e 0x1148d0 0x1203a3).toInstrSpec (call_rel32_effect_step 0x12039e 0xffff452d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12039b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12039e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1148d0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l120398 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120398 :=
  Rest.liftedBlock (rest_l120398 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120398 x hx)

theorem rest_l1203a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1203a3 bytes_l1203a3) (entryMap (live .l1203a3))
      5 0x1203a3 bytes_l1203a3 b_l1203a3 := by
  have f0 : InstrSpec 0x1203a3 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1203a3) (movR64R64Effect 0x1203a3 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1203a3 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1203a3 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1203a6 [0x48, 0x83, 0xC4, 0x58] (fun s => s.RIP = 0x1203a6) (addR64Imm8Effect 0x1203a6 4 0x58)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1203a6 4 0x58).toInstrSpec (add_r64_imm8_effect_step 0x1203a6 0x48 0xc4 0x58 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1203aa [0x5B] (PopPre 0x1203aa) (popR64Effect 0x1203aa 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1203aa 1 3).toInstrSpec (pop_r64_effect_step 0x1203aa 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1203ab [0x41, 0x5E] (PopPre 0x1203ab) (popR64Effect 0x1203ab 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1203ab 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1203ab 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1203ad [0xC3] (RetPre 0x1203ad) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1203ad).toInstrSpec (ret_effect_step 0x1203ad) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203a6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203aa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203ab) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1203ad) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l1203a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1203a3 :=
  Rest.liftedBlock (rest_l1203a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1203a3 x hx)

theorem rest_l120470_4 [Bindings] (code : CodeMap) :
    Rest (n := 201) code lifted (codeRange 0x120470 bytes_l120470) [(0, 197), (1, 82), (2, 194), (3, 120), (4, 199), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x120577 bytes_l120470_4 b_l120470_4 := by
  have f80 : InstrSpec 0x120577 [0x5B] (PopPre 0x120577) (popR64Effect 0x120577 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120577 1 3).toInstrSpec (pop_r64_effect_step 0x120577 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f81 : InstrSpec 0x120578 [0x41, 0x5C] (PopPre 0x120578) (popR64Effect 0x120578 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120578 2 12).toInstrSpec (pop_r64_rex_effect_step 0x120578 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f82 : InstrSpec 0x12057a [0x41, 0x5D] (PopPre 0x12057a) (popR64Effect 0x12057a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12057a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x12057a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f83 : InstrSpec 0x12057c [0x41, 0x5E] (PopPre 0x12057c) (popR64Effect 0x12057c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12057c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x12057c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f84 : InstrSpec 0x12057e [0x41, 0x5F] (PopPre 0x12057e) (popR64Effect 0x12057e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12057e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x12057e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f85 : InstrSpec 0x120580 [0x5D] (PopPre 0x120580) (popR64Effect 0x120580 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x120580 1 5).toInstrSpec (pop_r64_effect_step 0x120580 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f86 : InstrSpec 0x120581 [0xC3] (RetPre 0x120581) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x120581).toInstrSpec (ret_effect_step 0x120581) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f80 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 202) f80 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 203) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 202), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120578) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f81 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 205) f81 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 206) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 205), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12057a) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f82 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 208) f82 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 209) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 208), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12057c) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f83 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 211) f83 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 212) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 211), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 210), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12057e) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f84 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 214) f84 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 215) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 214), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 210), (15, 213), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120580) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f85 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 217) f85 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 218) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 217), (5, 216), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 210), (15, 213), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120581) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f86 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 220) f86 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 221) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 201), (4, 220), (5, 216), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 204), (13, 207), (14, 210), (15, 213), (22, 22), (39, 39), (50, 50), (51, 51)]) f86 (by decide) rfl rfl rfl (by decide)

theorem rest_l120470_3 [Bindings] (code : CodeMap) :
    Rest (n := 172) code lifted (codeRange 0x120470 bytes_l120470) [(0, 170), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]
      27 0x12052e bytes_l120470_3 b_l120470_3 := by
  have f60 : InstrSpec 0x12052e [0x0F, 0xB6, 0x76, 0x50] (LoadPre 0x12052e (fun s => AddrMode.addr (.base 6 (.d8 0x50)) s (0x12052e + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12052e 4 6 (.base 6 (.d8 0x50)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x12052e 4 6 (.base 6 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x12052e 6 (.base 6 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x120532 [0x0F, 0xB6, 0x52, 0x50] (LoadPre 0x120532 (fun s => AddrMode.addr (.base 2 (.d8 0x50)) s (0x120532 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x120532 4 2 (.base 2 (.d8 0x50)))
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x120532 4 2 (.base 2 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x120532 2 (.base 2 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f62 : InstrSpec 0x120536 [0x4C, 0x8B, 0x0C, 0x24] (LoadPre 0x120536 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x120536 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120536 9 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x120536 9 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x120536 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f63 : InstrSpec 0x12053a [0x41, 0xF6, 0xD9] (fun s => s.RIP = 0x12053a) (negR8Effect 0x12053a 3 9)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (negR8Effect_footprint 0x12053a 3 9).toInstrSpec (neg_r8_rex_effect_step 0x12053a 0x41 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x12053d [0x40, 0x30, 0xF2] (fun s => s.RIP = 0x12053d) (xorR8R8Effect 0x12053d 3 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR8R8Effect_footprint 0x12053d 3 2 6).toInstrSpec (xor_r8_r8_rex_effect_step 0x12053d 0x40 0xf2 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x120540 [0x44, 0x20, 0xCA] (fun s => s.RIP = 0x120540) (andR8R8Effect 0x120540 3 2 9)
      [.gpr 2, .gpr 9] [] [.reg 2, .flags, .rip] :=
    (andR8R8Effect_footprint 0x120540 3 2 9).toInstrSpec (and_r8_r8_rex_effect_step 0x120540 0x44 0xca (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x120543 [0x48, 0x89, 0x0F] (StorePre 0x120543 3 (fun s => AddrMode.addr (.base 7 .none) s (0x120543 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x120543 1 (.base 7 .none))
      [.gpr 1, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120543 1 (.base 7 .none)).toInstrSpec (mov_m64_r64_effect_step 0x120543 0x48 (by decide) 1 (.base 7 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x120546 [0x4C, 0x89, 0x47, 0x08] (StorePre 0x120546 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x120546 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120546 8 (.base 7 (.d8 0x8)))
      [.gpr 8, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120546 8 (.base 7 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x120546 0x4c (by decide) 0 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x12054a [0x4C, 0x89, 0x57, 0x10] (StorePre 0x12054a 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x12054a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12054a 10 (.base 7 (.d8 0x10)))
      [.gpr 10, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12054a 10 (.base 7 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12054a 0x4c (by decide) 2 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f69 : InstrSpec 0x12054e [0x4C, 0x89, 0x5F, 0x18] (StorePre 0x12054e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x12054e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12054e 11 (.base 7 (.d8 0x18)))
      [.gpr 11, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12054e 11 (.base 7 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x12054e 0x4c (by decide) 3 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x120552 [0x48, 0x89, 0x5F, 0x20] (StorePre 0x120552 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x120552 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120552 3 (.base 7 (.d8 0x20)))
      [.gpr 3, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120552 3 (.base 7 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x120552 0x48 (by decide) 3 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f71 : InstrSpec 0x120556 [0x4C, 0x89, 0x77, 0x28] (StorePre 0x120556 4 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x120556 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120556 14 (.base 7 (.d8 0x28)))
      [.gpr 14, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120556 14 (.base 7 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x120556 0x4c (by decide) 6 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x12055a [0x4C, 0x89, 0x7F, 0x30] (StorePre 0x12055a 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x12055a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12055a 15 (.base 7 (.d8 0x30)))
      [.gpr 15, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12055a 15 (.base 7 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x12055a 0x4c (by decide) 7 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x12055e [0x4C, 0x89, 0x67, 0x38] (StorePre 0x12055e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x12055e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12055e 12 (.base 7 (.d8 0x38)))
      [.gpr 12, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x12055e 12 (.base 7 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x12055e 0x4c (by decide) 4 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f74 : InstrSpec 0x120562 [0x4C, 0x89, 0x6F, 0x40] (StorePre 0x120562 4 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x120562 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120562 13 (.base 7 (.d8 0x40)))
      [.gpr 13, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120562 13 (.base 7 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x120562 0x4c (by decide) 5 (.base 7 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x120566 [0x48, 0x89, 0x47, 0x48] (StorePre 0x120566 4 (fun s => AddrMode.addr (.base 7 (.d8 0x48)) s (0x120566 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x120566 0 (.base 7 (.d8 0x48)))
      [.gpr 0, .gpr 7] [] [.rip] :=
    (movM64R64Effect_footprint 0x120566 0 (.base 7 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x120566 0x48 (by decide) 0 (.base 7 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x12056a [0x40, 0x30, 0xF2] (fun s => s.RIP = 0x12056a) (xorR8R8Effect 0x12056a 3 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR8R8Effect_footprint 0x12056a 3 2 6).toInstrSpec (xor_r8_r8_rex_effect_step 0x12056a 0x40 0xf2 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x12056d [0x88, 0x57, 0x50] (StorePre 0x12056d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x50)) s (0x12056d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12056d 3 2 (.base 7 (.d8 0x50)))
      [.gpr 2, .gpr 7] [] [.rip] :=
    (movM8R8Effect_footprint 0x12056d 3 2 (.base 7 (.d8 0x50))).toInstrSpec (mov_m8_r8_effect_step 0x12056d 2 (by decide) (.base 7 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x120570 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x120570) (movR64R64Effect 0x120570 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x120570 0 7).toInstrSpec (mov_r64_r64_effect_step 0x120570 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x120573 [0x48, 0x83, 0xC4, 0x08] (fun s => s.RIP = 0x120573) (addR64Imm8Effect 0x120573 4 0x8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x120573 4 0x8).toInstrSpec (add_r64_imm8_effect_step 0x120573 0x48 0xc4 0x8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f60 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 170), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120532) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f61 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 170), (1, 82), (2, 174), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120536) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f62 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 170), (1, 82), (2, 174), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 176), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12053a) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f63 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 170), (1, 82), (2, 174), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12053d) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.out (n := 180) f64 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 181) (ρ' := [(0, 170), (1, 82), (2, 180), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120540) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f65 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120543) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.exec (n := 184) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120546) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 185) (RestInside.exec (n := 185) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12054a) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12054e) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.exec (n := 187) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120552) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 188) (RestInside.exec (n := 188) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120556) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 189) (RestInside.exec (n := 189) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12055a) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 190) (RestInside.exec (n := 190) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12055e) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 191) (RestInside.exec (n := 191) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120562) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 192) (RestInside.exec (n := 192) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120566) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 193) (RestInside.exec (n := 193) (ρ' := [(0, 170), (1, 82), (2, 182), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12056a) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 170), (1, 82), (2, 194), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12056d) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.exec (n := 196) (ρ' := [(0, 170), (1, 82), (2, 194), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120570) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 120), (4, 65), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120573) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f79 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 197), (1, 82), (2, 194), (3, 120), (4, 199), (5, 162), (6, 172), (7, 7), (8, 90), (9, 178), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120577) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120470_4 code

theorem rest_l120470_2 [Bindings] (code : CodeMap) :
    Rest (n := 132) code lifted (codeRange 0x120470 bytes_l120470) [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 130), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]
      47 0x1204ea bytes_l120470_2 b_l120470_2 := by
  have f40 : InstrSpec 0x1204ea [0x4C, 0x8B, 0x66, 0x30] (LoadPre 0x1204ea (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x1204ea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204ea 12 (.base 6 (.d8 0x30)))
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1204ea 12 (.base 6 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1204ea 0x4c (by decide) 4 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x1204ee [0x4C, 0x8B, 0x7A, 0x30] (LoadPre 0x1204ee (fun s => AddrMode.addr (.base 2 (.d8 0x30)) s (0x1204ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204ee 15 (.base 2 (.d8 0x30)))
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1204ee 15 (.base 2 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1204ee 0x4c (by decide) 7 (.base 2 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x1204f2 [0x4D, 0x31, 0xE7] (fun s => s.RIP = 0x1204f2) (xorR64R64Effect 0x1204f2 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204f2 15 12).toInstrSpec (xor_r64_r64_effect_step 0x1204f2 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x1204f5 [0x4D, 0x21, 0xCF] (fun s => s.RIP = 0x1204f5) (andR64R64Effect 0x1204f5 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204f5 15 9).toInstrSpec (and_r64_r64_effect_step 0x1204f5 0x4d 0xcf (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1204f8 [0x4D, 0x31, 0xE7] (fun s => s.RIP = 0x1204f8) (xorR64R64Effect 0x1204f8 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204f8 15 12).toInstrSpec (xor_r64_r64_effect_step 0x1204f8 0x4d 0xe7 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x1204fb [0x4C, 0x8B, 0x6E, 0x38] (LoadPre 0x1204fb (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x1204fb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204fb 13 (.base 6 (.d8 0x38)))
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1204fb 13 (.base 6 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1204fb 0x4c (by decide) 5 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x1204ff [0x4C, 0x8B, 0x62, 0x38] (LoadPre 0x1204ff (fun s => AddrMode.addr (.base 2 (.d8 0x38)) s (0x1204ff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204ff 12 (.base 2 (.d8 0x38)))
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x1204ff 12 (.base 2 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x1204ff 0x4c (by decide) 4 (.base 2 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x120503 [0x4D, 0x31, 0xEC] (fun s => s.RIP = 0x120503) (xorR64R64Effect 0x120503 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120503 12 13).toInstrSpec (xor_r64_r64_effect_step 0x120503 0x4d 0xec (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x120506 [0x4D, 0x21, 0xCC] (fun s => s.RIP = 0x120506) (andR64R64Effect 0x120506 12 9)
      [.gpr 12, .gpr 9] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120506 12 9).toInstrSpec (and_r64_r64_effect_step 0x120506 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x120509 [0x4D, 0x31, 0xEC] (fun s => s.RIP = 0x120509) (xorR64R64Effect 0x120509 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120509 12 13).toInstrSpec (xor_r64_r64_effect_step 0x120509 0x4d 0xec (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x12050c [0x48, 0x8B, 0x6E, 0x40] (LoadPre 0x12050c (fun s => AddrMode.addr (.base 6 (.d8 0x40)) s (0x12050c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12050c 5 (.base 6 (.d8 0x40)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x12050c 5 (.base 6 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x12050c 0x48 (by decide) 5 (.base 6 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f51 : InstrSpec 0x120510 [0x4C, 0x8B, 0x6A, 0x40] (LoadPre 0x120510 (fun s => AddrMode.addr (.base 2 (.d8 0x40)) s (0x120510 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120510 13 (.base 2 (.d8 0x40)))
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x120510 13 (.base 2 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x120510 0x4c (by decide) 5 (.base 2 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f52 : InstrSpec 0x120514 [0x49, 0x31, 0xED] (fun s => s.RIP = 0x120514) (xorR64R64Effect 0x120514 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120514 13 5).toInstrSpec (xor_r64_r64_effect_step 0x120514 0x49 0xed (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x120517 [0x4D, 0x21, 0xCD] (fun s => s.RIP = 0x120517) (andR64R64Effect 0x120517 13 9)
      [.gpr 13, .gpr 9] [] [.reg 13, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120517 13 9).toInstrSpec (and_r64_r64_effect_step 0x120517 0x4d 0xcd (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x12051a [0x49, 0x31, 0xED] (fun s => s.RIP = 0x12051a) (xorR64R64Effect 0x12051a 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12051a 13 5).toInstrSpec (xor_r64_r64_effect_step 0x12051a 0x49 0xed (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x12051d [0x48, 0x8B, 0x6E, 0x48] (LoadPre 0x12051d (fun s => AddrMode.addr (.base 6 (.d8 0x48)) s (0x12051d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12051d 5 (.base 6 (.d8 0x48)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (movR64M64Effect_footprint 0x12051d 5 (.base 6 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x12051d 0x48 (by decide) 5 (.base 6 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f56 : InstrSpec 0x120521 [0x48, 0x8B, 0x42, 0x48] (LoadPre 0x120521 (fun s => AddrMode.addr (.base 2 (.d8 0x48)) s (0x120521 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120521 0 (.base 2 (.d8 0x48)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x120521 0 (.base 2 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x120521 0x48 (by decide) 0 (.base 2 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f57 : InstrSpec 0x120525 [0x48, 0x31, 0xE8] (fun s => s.RIP = 0x120525) (xorR64R64Effect 0x120525 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120525 0 5).toInstrSpec (xor_r64_r64_effect_step 0x120525 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x120528 [0x4C, 0x21, 0xC8] (fun s => s.RIP = 0x120528) (andR64R64Effect 0x120528 0 9)
      [.gpr 0, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120528 0 9).toInstrSpec (and_r64_r64_effect_step 0x120528 0x4c 0xc8 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x12052b [0x48, 0x31, 0xE8] (fun s => s.RIP = 0x12052b) (xorR64R64Effect 0x12052b 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12052b 0 5).toInstrSpec (xor_r64_r64_effect_step 0x12052b 0x48 0xe8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f40 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204ee) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f41 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204f2) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f42 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 136), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204f5) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f43 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204f8) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 13), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204fb) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f45 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 132), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204ff) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f46 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 144), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120503) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f47 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 146), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120506) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f48 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 148), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120509) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f49 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12050c) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f50 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 142), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120510) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f51 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 154), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120514) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f52 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 156), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120517) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f53 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 158), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12051a) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f54 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 152), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12051d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f55 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120521) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f56 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 164), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120525) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f57 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 166), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120528) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f58 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 168), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12052b) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f59 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 170), (1, 82), (2, 2), (3, 120), (4, 65), (5, 162), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 150), (13, 160), (14, 130), (15, 140), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12052e) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120470_3 code

theorem rest_l120470_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x120470 bytes_l120470) [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      67 0x1204a6 bytes_l120470_1 b_l120470_1 := by
  have f20 : InstrSpec 0x1204a6 [0x4C, 0x8B, 0x5E, 0x10] (LoadPre 0x1204a6 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1204a6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204a6 11 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1204a6 11 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1204a6 0x4c (by decide) 3 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x1204aa [0x4C, 0x8B, 0x52, 0x10] (LoadPre 0x1204aa (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1204aa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204aa 10 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1204aa 10 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1204aa 0x4c (by decide) 2 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x1204ae [0x4D, 0x31, 0xDA] (fun s => s.RIP = 0x1204ae) (xorR64R64Effect 0x1204ae 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204ae 10 11).toInstrSpec (xor_r64_r64_effect_step 0x1204ae 0x4d 0xda (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1204b1 [0x4D, 0x21, 0xCA] (fun s => s.RIP = 0x1204b1) (andR64R64Effect 0x1204b1 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204b1 10 9).toInstrSpec (and_r64_r64_effect_step 0x1204b1 0x4d 0xca (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1204b4 [0x4D, 0x31, 0xDA] (fun s => s.RIP = 0x1204b4) (xorR64R64Effect 0x1204b4 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204b4 10 11).toInstrSpec (xor_r64_r64_effect_step 0x1204b4 0x4d 0xda (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1204b7 [0x48, 0x8B, 0x5E, 0x18] (LoadPre 0x1204b7 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1204b7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204b7 3 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1204b7 3 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1204b7 0x48 (by decide) 3 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x1204bb [0x4C, 0x8B, 0x5A, 0x18] (LoadPre 0x1204bb (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1204bb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204bb 11 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1204bb 11 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1204bb 0x4c (by decide) 3 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x1204bf [0x49, 0x31, 0xDB] (fun s => s.RIP = 0x1204bf) (xorR64R64Effect 0x1204bf 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204bf 11 3).toInstrSpec (xor_r64_r64_effect_step 0x1204bf 0x49 0xdb (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1204c2 [0x4D, 0x21, 0xCB] (fun s => s.RIP = 0x1204c2) (andR64R64Effect 0x1204c2 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204c2 11 9).toInstrSpec (and_r64_r64_effect_step 0x1204c2 0x4d 0xcb (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1204c5 [0x49, 0x31, 0xDB] (fun s => s.RIP = 0x1204c5) (xorR64R64Effect 0x1204c5 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204c5 11 3).toInstrSpec (xor_r64_r64_effect_step 0x1204c5 0x49 0xdb (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1204c8 [0x4C, 0x8B, 0x76, 0x20] (LoadPre 0x1204c8 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1204c8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204c8 14 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1204c8 14 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1204c8 0x4c (by decide) 6 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x1204cc [0x48, 0x8B, 0x5A, 0x20] (LoadPre 0x1204cc (fun s => AddrMode.addr (.base 2 (.d8 0x20)) s (0x1204cc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204cc 3 (.base 2 (.d8 0x20)))
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1204cc 3 (.base 2 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x1204cc 0x48 (by decide) 3 (.base 2 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x1204d0 [0x4C, 0x31, 0xF3] (fun s => s.RIP = 0x1204d0) (xorR64R64Effect 0x1204d0 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204d0 3 14).toInstrSpec (xor_r64_r64_effect_step 0x1204d0 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x1204d3 [0x4C, 0x21, 0xCB] (fun s => s.RIP = 0x1204d3) (andR64R64Effect 0x1204d3 3 9)
      [.gpr 3, .gpr 9] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204d3 3 9).toInstrSpec (and_r64_r64_effect_step 0x1204d3 0x4c 0xcb (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1204d6 [0x4C, 0x31, 0xF3] (fun s => s.RIP = 0x1204d6) (xorR64R64Effect 0x1204d6 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204d6 3 14).toInstrSpec (xor_r64_r64_effect_step 0x1204d6 0x4c 0xf3 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x1204d9 [0x4C, 0x8B, 0x7E, 0x28] (LoadPre 0x1204d9 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x1204d9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204d9 15 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1204d9 15 (.base 6 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1204d9 0x4c (by decide) 7 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x1204dd [0x4C, 0x8B, 0x72, 0x28] (LoadPre 0x1204dd (fun s => AddrMode.addr (.base 2 (.d8 0x28)) s (0x1204dd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1204dd 14 (.base 2 (.d8 0x28)))
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1204dd 14 (.base 2 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x1204dd 0x4c (by decide) 6 (.base 2 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x1204e1 [0x4D, 0x31, 0xFE] (fun s => s.RIP = 0x1204e1) (xorR64R64Effect 0x1204e1 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204e1 14 15).toInstrSpec (xor_r64_r64_effect_step 0x1204e1 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1204e4 [0x4D, 0x21, 0xCE] (fun s => s.RIP = 0x1204e4) (andR64R64Effect 0x1204e4 14 9)
      [.gpr 14, .gpr 9] [] [.reg 14, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204e4 14 9).toInstrSpec (and_r64_r64_effect_step 0x1204e4 0x4d 0xce (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x1204e7 [0x4D, 0x31, 0xFE] (fun s => s.RIP = 0x1204e7) (xorR64R64Effect 0x1204e7 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204e7 14 15).toInstrSpec (xor_r64_r64_effect_step 0x1204e7 0x4d 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 74), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204aa) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 94), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204ae) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 96), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204b1) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 98), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204b4) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204b7) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 92), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204bb) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 104), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204bf) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 106), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204c2) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 108), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204c5) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f29 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204c8) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f30 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 102), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204cc) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f31 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 114), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204d0) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f32 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 116), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204d3) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f33 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 118), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204d6) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f34 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204d9) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f35 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 112), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204dd) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f36 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 124), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204e1) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f37 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 126), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204e4) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f38 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 128), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204e7) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f39 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 120), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 100), (11, 110), (12, 12), (13, 13), (14, 130), (15, 122), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204ea) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120470_2 code

theorem rest_l120470 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120470 bytes_l120470) (entryMap (live .l120470))
      87 0x120470 bytes_l120470 b_l120470 := by
  have f0 : InstrSpec 0x120470 [0x55] (PushPre 0x120470 1) (pushR64Effect 0x120470 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120470 1 5).toInstrSpec (push_r64_effect_step 0x120470 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x120471 [0x41, 0x57] (PushPre 0x120471 2) (pushR64Effect 0x120471 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120471 2 15).toInstrSpec (push_r64_rex_effect_step 0x120471 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x120473 [0x41, 0x56] (PushPre 0x120473 2) (pushR64Effect 0x120473 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120473 2 14).toInstrSpec (push_r64_rex_effect_step 0x120473 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x120475 [0x41, 0x55] (PushPre 0x120475 2) (pushR64Effect 0x120475 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120475 2 13).toInstrSpec (push_r64_rex_effect_step 0x120475 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x120477 [0x41, 0x54] (PushPre 0x120477 2) (pushR64Effect 0x120477 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120477 2 12).toInstrSpec (push_r64_rex_effect_step 0x120477 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x120479 [0x53] (PushPre 0x120479 1) (pushR64Effect 0x120479 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120479 1 3).toInstrSpec (push_r64_effect_step 0x120479 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12047a [0x50] (PushPre 0x12047a 1) (pushR64Effect 0x12047a 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12047a 1 0).toInstrSpec (push_r64_effect_step 0x12047a 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x12047b [0x44, 0x0F, 0xB6, 0xC9] (fun s => s.RIP = 0x12047b) (movzxR32R8Effect 0x12047b 4 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movzxR32R8Effect_footprint 0x12047b 4 9 1).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12047b 0x44 (by decide) 0xc9 (by decide)) pre_rip
  have f8 : InstrSpec 0x12047f [0x4C, 0x89, 0x0C, 0x24] (StorePre 0x12047f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x12047f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12047f 9 (.sib 4 none 0 .none))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12047f 9 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x12047f 0x4c (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x120483 [0x49, 0xF7, 0xD9] (fun s => s.RIP = 0x120483) (negR64Effect 0x120483 9)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (negR64Effect_footprint 0x120483 9).toInstrSpec (neg_r64_effect_step 0x120483 0x49 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x120486 [0x4C, 0x8B, 0x06] (LoadPre 0x120486 (fun s => AddrMode.addr (.base 6 .none) s (0x120486 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x120486 8 (.base 6 .none))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x120486 8 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x120486 0x4c (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x120489 [0x4C, 0x8B, 0x56, 0x08] (LoadPre 0x120489 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x120489 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120489 10 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x120489 10 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x120489 0x4c (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12048d [0x48, 0x8B, 0x0A] (LoadPre 0x12048d (fun s => AddrMode.addr (.base 2 .none) s (0x12048d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12048d 1 (.base 2 .none))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12048d 1 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12048d 0x48 (by decide) 1 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x120490 [0x4C, 0x31, 0xC1] (fun s => s.RIP = 0x120490) (xorR64R64Effect 0x120490 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120490 1 8).toInstrSpec (xor_r64_r64_effect_step 0x120490 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x120493 [0x4C, 0x21, 0xC9] (fun s => s.RIP = 0x120493) (andR64R64Effect 0x120493 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x120493 1 9).toInstrSpec (and_r64_r64_effect_step 0x120493 0x4c 0xc9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x120496 [0x4C, 0x31, 0xC1] (fun s => s.RIP = 0x120496) (xorR64R64Effect 0x120496 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x120496 1 8).toInstrSpec (xor_r64_r64_effect_step 0x120496 0x4c 0xc1 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x120499 [0x4C, 0x8B, 0x42, 0x08] (LoadPre 0x120499 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x120499 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120499 8 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x120499 8 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x120499 0x4c (by decide) 0 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x12049d [0x4D, 0x31, 0xD0] (fun s => s.RIP = 0x12049d) (xorR64R64Effect 0x12049d 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12049d 8 10).toInstrSpec (xor_r64_r64_effect_step 0x12049d 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1204a0 [0x4D, 0x21, 0xC8] (fun s => s.RIP = 0x1204a0) (andR64R64Effect 0x1204a0 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1204a0 8 9).toInstrSpec (and_r64_r64_effect_step 0x1204a0 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1204a3 [0x4D, 0x31, 0xD0] (fun s => s.RIP = 0x1204a3) (xorR64R64Effect 0x1204a3 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1204a3 8 10).toInstrSpec (xor_r64_r64_effect_step 0x1204a3 0x4d 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120471) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120473) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120475) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120477) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120479) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12047a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12047b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12047f) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 67), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120483) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 70), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120486) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120489) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12048d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 76), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120490) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 78), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120493) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 80), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120496) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120499) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 84), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12049d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 86), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204a0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 88), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204a3) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 90), (9, 70), (10, 74), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1204a6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120470_1 code

theorem block_l120470 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120470 :=
  Rest.liftedBlock (rest_l120470 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120470 x hx)

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

theorem rest_l127f50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f50 bytes_l127f50) (entryMap (live .l127f50))
      2 0x127f50 bytes_l127f50 b_l127f50 := by
  have f0 : InstrSpec 0x127f50 [0x48, 0x39, 0xCE] (fun s => s.RIP = 0x127f50) (cmpR64R64Effect 0x127f50 6 1)
      [.gpr 6, .gpr 1] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127f50 6 1).toInstrSpec (cmp_r64_r64_effect_step 0x127f50 0x48 0xce (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f53) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127f53 5 0x45) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127f50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f50 :=
  Rest.liftedBlock (rest_l127f50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f50 x hx)

theorem rest_l127f55 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f55 bytes_l127f55) (entryMap (live .l127f55))
      2 0x127f55 bytes_l127f55 b_l127f55 := by
  have f0 : InstrSpec 0x127f55 [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x127f55) (testR64R64Effect 0x127f55 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x127f55 6 6).toInstrSpec (test_r64_r64_effect_step 0x127f55 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f58) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x127f58 4 0x4f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127f55 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f55 :=
  Rest.liftedBlock (rest_l127f55 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f55 x hx)

theorem rest_l127f5a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f5a bytes_l127f5a) (entryMap (live .l127f5a))
      4 0x127f5a bytes_l127f5a b_l127f5a := by
  have f0 : InstrSpec 0x127f5a [0x66, 0xB8, 0x01, 0x00] (fun s => s.RIP = 0x127f5a) (movR16Imm16Effect 0x127f5a 4 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR16Imm16Effect_footprint 0x127f5a 4 0 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127f5a 0xb8 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x127f5e [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x127f5e) (xorR32R32Effect 0x127f5e 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f5e 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x127f5e 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127f61 [0x31, 0xC9] (fun s => s.RIP = 0x127f61) (xorR32R32Effect 0x127f61 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f61 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x127f61 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x127f63 [0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127f63) (fun _ => nopEffect 0x127f63 13)
      [] [] [.rip] :=
    (nopEffect_footprint 0x127f63 13).toInstrSpec (nop_m_effect_step 0x127f63 [0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f5e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f61) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f63) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f70) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l127f5a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f5a :=
  Rest.liftedBlock (rest_l127f5a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f5a x hx)

theorem rest_l127f70 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f70 bytes_l127f70) (entryMap (live .l127f70))
      8 0x127f70 bytes_l127f70 b_l127f70 := by
  have f0 : InstrSpec 0x127f70 [0x4E, 0x8B, 0x0C, 0xC7] (LoadPre 0x127f70 (fun s => AddrMode.addr (.sib 7 (some 8) 3 .none) s (0x127f70 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127f70 9 (.sib 7 (some 8) 3 .none))
      [.gpr 7, .gpr 8] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x127f70 9 (.sib 7 (some 8) 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x127f70 0x4e (by decide) 1 (.sib 7 (some 8) 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127f74 [0x4E, 0x8B, 0x14, 0xC2] (LoadPre 0x127f74 (fun s => AddrMode.addr (.sib 2 (some 8) 3 .none) s (0x127f74 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127f74 10 (.sib 2 (some 8) 3 .none))
      [.gpr 2, .gpr 8] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x127f74 10 (.sib 2 (some 8) 3 .none)).toInstrSpec (mov_r64_m64_effect_step 0x127f74 0x4e (by decide) 2 (.sib 2 (some 8) 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x127f78 [0x49, 0xFF, 0xC0] (fun s => s.RIP = 0x127f78) (incR64Effect 0x127f78 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (incR64Effect_footprint 0x127f78 8).toInstrSpec (inc_r64_effect_step 0x127f78 0x49 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127f7b [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x127f7b) (movzxR32R8Effect 0x127f7b 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x127f7b 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x127f7b 0xc0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127f7e [0x4D, 0x31, 0xD1] (fun s => s.RIP = 0x127f7e) (xorR64R64Effect 0x127f7e 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x127f7e 9 10).toInstrSpec (xor_r64_r64_effect_step 0x127f7e 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x127f81 [0x48, 0x0F, 0x45, 0xC1] (fun s => s.RIP = 0x127f81) (atFlags (condHolds 5) (cmovR64R64Effect 0x127f81 4 0 1))
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR64R64Effect_footprint 0x127f81 4 0 1 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x127f81 5 0x48 (by decide) 0xc1 (by decide) c)) pre_rip
  have f6 : InstrSpec 0x127f85 [0x4C, 0x39, 0xC6] (fun s => s.RIP = 0x127f85) (cmpR64R64Effect 0x127f85 6 8)
      [.gpr 6, .gpr 8] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x127f85 6 8).toInstrSpec (cmp_r64_r64_effect_step 0x127f85 0x4c 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f74) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f78) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f7b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 53), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f7e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 61), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f81) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 61), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f85) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 61), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f88) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel8_effect_step 0x127f88 5 0xe6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127f70 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f70 :=
  Rest.liftedBlock (rest_l127f70 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f70 x hx)

theorem rest_l127f8a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f8a bytes_l127f8a) (entryMap (live .l127f8a))
      6 0x127f8a bytes_l127f8a b_l127f8a := by
  have f0 : InstrSpec 0x127f8a [0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x127f8a) (movzxR32R8Effect 0x127f8a 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x127f8a 3 1 0).toInstrSpec (movzx_r32_r8_effect_step 0x127f8a 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127f8d [0x31, 0xC0] (fun s => s.RIP = 0x127f8d) (xorR32R32Effect 0x127f8d 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f8d 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x127f8d 0xc0 (by decide)) pre_rip
  have f2 : InstrSpec 0x127f8f [0x66, 0xBA, 0x01, 0x00] (fun s => s.RIP = 0x127f8f) (movR16Imm16Effect 0x127f8f 4 2 0x1)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR16Imm16Effect_footprint 0x127f8f 4 2 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127f8f 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x127f93 [0x66, 0x31, 0xD1] (fun s => s.RIP = 0x127f93) (xorR16R16Effect 0x127f93 3 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x127f93 3 1 2).toInstrSpec (xor_r16_r16_effect_step 0x127f93 0xd1 (by decide)) pre_rip
  have f4 : InstrSpec 0x127f96 [0x0F, 0x44, 0xC2] (fun s => s.RIP = 0x127f96) (atFlags (condHolds 4) (cmovR32R32Effect 0x127f96 3 0 2))
      [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR32R32Effect_footprint 0x127f96 3 0 2 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x127f96 4 0xc2 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x127f99 [0xC3] (RetPre 0x127f99) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127f99).toInstrSpec (ret_effect_step 0x127f99) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f8d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f8f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f93) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f96) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f99) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 66) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127f8a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f8a :=
  Rest.liftedBlock (rest_l127f8a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f8a x hx)

theorem rest_l127f9a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127f9a bytes_l127f9a) (entryMap (live .l127f9a))
      6 0x127f9a bytes_l127f9a b_l127f9a := by
  have f0 : InstrSpec 0x127f9a [0x31, 0xC9] (fun s => s.RIP = 0x127f9a) (xorR32R32Effect 0x127f9a 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f9a 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x127f9a 0xc9 (by decide)) pre_rip
  have f1 : InstrSpec 0x127f9c [0x31, 0xC0] (fun s => s.RIP = 0x127f9c) (xorR32R32Effect 0x127f9c 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127f9c 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x127f9c 0xc0 (by decide)) pre_rip
  have f2 : InstrSpec 0x127f9e [0x66, 0xBA, 0x01, 0x00] (fun s => s.RIP = 0x127f9e) (movR16Imm16Effect 0x127f9e 4 2 0x1)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR16Imm16Effect_footprint 0x127f9e 4 2 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127f9e 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x127fa2 [0x66, 0x31, 0xD1] (fun s => s.RIP = 0x127fa2) (xorR16R16Effect 0x127fa2 3 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x127fa2 3 1 2).toInstrSpec (xor_r16_r16_effect_step 0x127fa2 0xd1 (by decide)) pre_rip
  have f4 : InstrSpec 0x127fa5 [0x0F, 0x44, 0xC2] (fun s => s.RIP = 0x127fa5) (atFlags (condHolds 4) (cmovR32R32Effect 0x127fa5 3 0 2))
      [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR32R32Effect_footprint 0x127fa5 3 0 2 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x127fa5 4 0xc2 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x127fa8 [0xC3] (RetPre 0x127fa8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127fa8).toInstrSpec (ret_effect_step 0x127fa8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f9c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127f9e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fa2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fa5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fa8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 66) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127f9a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127f9a :=
  Rest.liftedBlock (rest_l127f9a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127f9a x hx)

theorem rest_l127fa9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127fa9 bytes_l127fa9) (entryMap (live .l127fa9))
      6 0x127fa9 bytes_l127fa9 b_l127fa9 := by
  have f0 : InstrSpec 0x127fa9 [0x66, 0xB9, 0x01, 0x00] (fun s => s.RIP = 0x127fa9) (movR16Imm16Effect 0x127fa9 4 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR16Imm16Effect_footprint 0x127fa9 4 1 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127fa9 0xb9 (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x127fad [0x31, 0xC0] (fun s => s.RIP = 0x127fad) (xorR32R32Effect 0x127fad 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127fad 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x127fad 0xc0 (by decide)) pre_rip
  have f2 : InstrSpec 0x127faf [0x66, 0xBA, 0x01, 0x00] (fun s => s.RIP = 0x127faf) (movR16Imm16Effect 0x127faf 4 2 0x1)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR16Imm16Effect_footprint 0x127faf 4 2 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x127faf 0xba (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x127fb3 [0x66, 0x31, 0xD1] (fun s => s.RIP = 0x127fb3) (xorR16R16Effect 0x127fb3 3 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x127fb3 3 1 2).toInstrSpec (xor_r16_r16_effect_step 0x127fb3 0xd1 (by decide)) pre_rip
  have f4 : InstrSpec 0x127fb6 [0x0F, 0x44, 0xC2] (fun s => s.RIP = 0x127fb6) (atFlags (condHolds 4) (cmovR32R32Effect 0x127fb6 3 0 2))
      [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (cmovR32R32Effect_footprint 0x127fb6 3 0 2 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_effect_step 0x127fb6 4 0xc2 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x127fb9 [0xC3] (RetPre 0x127fb9) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x127fb9).toInstrSpec (ret_effect_step 0x127fb9) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fad) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127faf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fb3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fb6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fb9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 66) (ρ' := [(0, 62), (1, 59), (2, 57), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l127fa9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127fa9 :=
  Rest.liftedBlock (rest_l127fa9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127fa9 x hx)

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

theorem_by block_l100a30_eval :
    program.runBlock (dialect code) ⟨.l100a30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108890_eval :
    program.runBlock (dialect code) ⟨.l108890, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1088a6_eval :
    program.runBlock (dialect code) ⟨.l1088a6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1088b6_eval :
    program.runBlock (dialect code) ⟨.l1088b6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1088bb_eval :
    program.runBlock (dialect code) ⟨.l1088bb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1088c3_eval :
    program.runBlock (dialect code) ⟨.l1088c3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10893a_eval :
    program.runBlock (dialect code) ⟨.l10893a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l108952_eval :
    program.runBlock (dialect code) ⟨.l108952, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10896a_eval :
    program.runBlock (dialect code) ⟨.l10896a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109e60_eval :
    program.runBlock (dialect code) ⟨.l109e60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109f32_eval :
    program.runBlock (dialect code) ⟨.l109f32, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a220_eval :
    program.runBlock (dialect code) ⟨.l10a220, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a280_eval :
    program.runBlock (dialect code) ⟨.l10a280, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a293_eval :
    program.runBlock (dialect code) ⟨.l10a293, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fa10_eval :
    program.runBlock (dialect code) ⟨.l10fa10, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fa68_eval :
    program.runBlock (dialect code) ⟨.l10fa68, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fe50_eval :
    program.runBlock (dialect code) ⟨.l10fe50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ff00_eval :
    program.runBlock (dialect code) ⟨.l10ff00, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ff24_eval :
    program.runBlock (dialect code) ⟨.l10ff24, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ff59_eval :
    program.runBlock (dialect code) ⟨.l10ff59, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10ffb3_eval :
    program.runBlock (dialect code) ⟨.l10ffb3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110070_eval :
    program.runBlock (dialect code) ⟨.l110070, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110085_eval :
    program.runBlock (dialect code) ⟨.l110085, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110090_eval :
    program.runBlock (dialect code) ⟨.l110090, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l110b80_eval :
    program.runBlock (dialect code) ⟨.l110b80, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1148d0_eval :
    program.runBlock (dialect code) ⟨.l1148d0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120350_eval :
    program.runBlock (dialect code) ⟨.l120350, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120398_eval :
    program.runBlock (dialect code) ⟨.l120398, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1203a3_eval :
    program.runBlock (dialect code) ⟨.l1203a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120470_eval :
    program.runBlock (dialect code) ⟨.l120470, args, mem⟩ = _ := by
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

theorem_by block_l127f50_eval :
    program.runBlock (dialect code) ⟨.l127f50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f55_eval :
    program.runBlock (dialect code) ⟨.l127f55, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f5a_eval :
    program.runBlock (dialect code) ⟨.l127f5a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f70_eval :
    program.runBlock (dialect code) ⟨.l127f70, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f8a_eval :
    program.runBlock (dialect code) ⟨.l127f8a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127f9a_eval :
    program.runBlock (dialect code) ⟨.l127f9a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127fa9_eval :
    program.runBlock (dialect code) ⟨.l127fa9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
