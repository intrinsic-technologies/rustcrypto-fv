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

theorem rest_l127fc0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127fc0 bytes_l127fc0) (entryMap (live .l127fc0))
      4 0x127fc0 bytes_l127fc0 b_l127fc0 := by
  have f0 : InstrSpec 0x127fc0 [0x53] (PushPre 0x127fc0 1) (pushR64Effect 0x127fc0 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x127fc0 1 3).toInstrSpec (push_r64_effect_step 0x127fc0 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x127fc1 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x127fc1) (movR64R64Effect 0x127fc1 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x127fc1 0 7).toInstrSpec (mov_r64_r64_effect_step 0x127fc1 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127fc4 [0x48, 0x85, 0xD2] (fun s => s.RIP = 0x127fc4) (testR64R64Effect 0x127fc4 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x127fc4 2 2).toInstrSpec (test_r64_r64_effect_step 0x127fc4 0x48 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fc1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fc4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fc7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x127fc7 4 0x198) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127fc0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127fc0 :=
  Rest.liftedBlock (rest_l127fc0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127fc0 x hx)

theorem rest_l127fcd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127fcd bytes_l127fcd) (entryMap (live .l127fcd))
      6 0x127fcd bytes_l127fcd b_l127fcd := by
  have f0 : InstrSpec 0x127fcd [0x0F, 0xB6, 0x0E] (LoadPre 0x127fcd (fun s => AddrMode.addr (.base 6 .none) s (0x127fcd + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x127fcd 3 1 (.base 6 .none))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x127fcd 3 1 (.base 6 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x127fcd 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x127fd0 [0x69, 0xF9, 0xCD, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x127fd0) (imulR32R32Imm32Effect 0x127fd0 6 7 1 0xcd)
      [.gpr 1] [] [.reg 7, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x127fd0 6 7 1 0xcd).toInstrSpec (imul_r32_r32_imm32_effect_step 0x127fd0 0xf9 (by decide) 0xcd) pre_rip
  have f2 : InstrSpec 0x127fd6 [0xC1, 0xEF, 0x0D] (fun s => s.RIP = 0x127fd6) (shrR32Effect 0x127fd6 3 7 13)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x127fd6 3 7 13).toInstrSpec (shr_r32_imm8_effect_step 0x127fd6 0xef 0xd (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x127fd9 [0x48, 0xC1, 0xE7, 0x20] (fun s => s.RIP = 0x127fd9) (shlR64Effect 0x127fd9 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64Effect_footprint 0x127fd9 4 7 32).toInstrSpec (shl_r64_imm8_effect_step 0x127fd9 0x48 0xe7 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x127fdd [0x66, 0x83, 0xF9, 0x77] (fun s => s.RIP = 0x127fdd) (cmpR16Imm8Effect 0x127fdd 4 1 0x77)
      [.gpr 1] [] [.flags, .rip] :=
    (cmpR16Imm8Effect_footprint 0x127fdd 4 1 0x77).toInstrSpec (cmp_r16_imm8_effect_step 0x127fdd 0xf9 0x77 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fd0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fd6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fd9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fdd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fe1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 64) (jcc_rel32_effect_step 0x127fe1 7 0x190) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l127fcd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127fcd :=
  Rest.liftedBlock (rest_l127fcd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127fcd x hx)

theorem rest_l127fe7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x127fe7 bytes_l127fe7) (entryMap (live .l127fe7))
      4 0x127fe7 bytes_l127fe7 b_l127fe7 := by
  have f0 : InstrSpec 0x127fe7 [0x48, 0x83, 0xCF, 0x01] (fun s => s.RIP = 0x127fe7) (orR64Imm8Effect 0x127fe7 7 0x1)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x127fe7 7 0x1).toInstrSpec (or_r64_imm8_effect_step 0x127fe7 0x48 0xcf 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x127feb [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x127feb) (xorR32R32Effect 0x127feb 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x127feb 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x127feb 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x127fee [0x48, 0xB9, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x127fee) (movR64Imm64Effect 0x127fee 1 0xffffffff00000000)
      [] [] [.reg 1, .rip] :=
    (movR64Imm64Effect_footprint 0x127fee 1 0xffffffff00000000).toInstrSpec (mov_r64_imm64_effect_step 0x127fee 0x48 0xb9 (by decide) (by decide) 0xffffffff00000000) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127feb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127fee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127ff8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x127ff8 0x18 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l127fe7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l127fe7 :=
  Rest.liftedBlock (rest_l127fe7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l127fe7 x hx)

theorem rest_l128000 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128000 bytes_l128000) (entryMap (live .l128000))
      2 0x128000 bytes_l128000 b_l128000 := by
  have f0 : InstrSpec 0x128000 [0x48, 0x21, 0xCF] (fun s => s.RIP = 0x128000) (andR64R64Effect 0x128000 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (andR64R64Effect_footprint 0x128000 7 1).toInstrSpec (and_r64_r64_effect_step 0x128000 0x48 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128003 [0x49, 0x89, 0xF9] (fun s => s.RIP = 0x128003) (movR64R64Effect 0x128003 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x128003 9 7).toInstrSpec (mov_r64_r64_effect_step 0x128003 0x49 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128003) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128006) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l128000 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128000 :=
  Rest.liftedBlock (rest_l128000 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128000 x hx)

theorem rest_l128006 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128006 bytes_l128006) (entryMap (live .l128006))
      3 0x128006 bytes_l128006 b_l128006 := by
  have f0 : InstrSpec 0x128006 [0x4C, 0x89, 0xCF] (fun s => s.RIP = 0x128006) (movR64R64Effect 0x128006 7 9)
      [.gpr 9] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128006 7 9).toInstrSpec (mov_r64_r64_effect_step 0x128006 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128009 [0x45, 0x85, 0xC9] (fun s => s.RIP = 0x128009) (testR32R32Effect 0x128009 3 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x128009 3 9 9).toInstrSpec (test_r32_r32_rex_effect_step 0x128009 0x45 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128009) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12800c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x12800c 4 0x178) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128006 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128006 :=
  Rest.liftedBlock (rest_l128006 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128006 x hx)

theorem rest_l128012 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128012 bytes_l128012) (entryMap (live .l128012))
      2 0x128012 bytes_l128012 b_l128012 := by
  have f0 : InstrSpec 0x128012 [0x4D, 0x85, 0xC0] (fun s => s.RIP = 0x128012) (testR64R64Effect 0x128012 8 8)
      [.gpr 8, .gpr 8] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128012 8 8).toInstrSpec (test_r64_r64_effect_step 0x128012 0x4d 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128015) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x128015 4 0x115) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128012 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128012 :=
  Rest.liftedBlock (rest_l128012 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128012 x hx)

theorem rest_l12801b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12801b bytes_l12801b) (entryMap (live .l12801b))
      2 0x12801b bytes_l12801b b_l12801b := by
  have f0 : InstrSpec 0x12801b [0x49, 0x39, 0xD0] (fun s => s.RIP = 0x12801b) (cmpR64R64Effect 0x12801b 8 2)
      [.gpr 8, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12801b 8 2).toInstrSpec (cmp_r64_r64_effect_step 0x12801b 0x49 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12801e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12801e 3 0xe0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12801b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12801b :=
  Rest.liftedBlock (rest_l12801b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12801b x hx)

theorem rest_l128020 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128020 bytes_l128020) (entryMap (live .l128020))
      6 0x128020 bytes_l128020 b_l128020 := by
  have f0 : InstrSpec 0x128020 [0x46, 0x0F, 0xB6, 0x0C, 0x06] (LoadPre 0x128020 (fun s => AddrMode.addr (.sib 6 (some 8) 0 .none) s (0x128020 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x128020 5 9 (.sib 6 (some 8) 0 .none))
      [.gpr 6, .gpr 8] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x128020 5 9 (.sib 6 (some 8) 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x128020 0x46 (by decide) 1 (.sib 6 (some 8) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128025 [0x45, 0x89, 0xCB] (fun s => s.RIP = 0x128025) (movR32R32Effect 0x128025 3 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x128025 3 11 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x128025 0x45 0xcb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128028 [0x41, 0x83, 0xE1, 0x7F] (fun s => s.RIP = 0x128028) (andR32Imm8Effect 0x128028 4 9 0x7f)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x128028 4 9 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x128028 0x41 0xe1 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12802c [0x41, 0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12802c) (movR32Imm32Effect 0x12802c 6 10 0x1)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x12802c 6 10 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x12802c 0x41 0xba (by decide) (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x128032 [0x45, 0x84, 0xDB] (fun s => s.RIP = 0x128032) (testR8R8Effect 0x128032 3 11 11)
      [.gpr 11, .gpr 11] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128032 3 11 11).toInstrSpec (test_r8_r8_rex_effect_step 0x128032 0x45 0xdb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128025) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128028) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12802c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (10, 59), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128032) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (10, 59), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128035) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel32_effect_step 0x128035 9 0xe5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128020 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128020 :=
  Rest.liftedBlock (rest_l128020 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128020 x hx)

theorem rest_l12803b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12803b bytes_l12803b) (entryMap (live .l12803b))
      3 0x12803b bytes_l12803b b_l12803b := by
  have f0 : InstrSpec 0x12803b [0x4D, 0x8D, 0x50, 0x01] (fun s => s.RIP = 0x12803b) (leaR64Effect 0x12803b 10 (.base 8 (.d8 0x1)))
      [.gpr 8] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x12803b 10 (.base 8 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x12803b 0x4d (by decide) 2 (.base 8 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12803f [0x49, 0x39, 0xD2] (fun s => s.RIP = 0x12803f) (cmpR64R64Effect 0x12803f 10 2)
      [.gpr 10, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12803f 10 2).toInstrSpec (cmp_r64_r64_effect_step 0x12803f 0x49 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12803f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128042) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x128042 3 0x158) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12803b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12803b :=
  Rest.liftedBlock (rest_l12803b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12803b x hx)

theorem rest_l128048 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128048 bytes_l128048) (entryMap (live .l128048))
      9 0x128048 bytes_l128048 b_l128048 := by
  have f0 : InstrSpec 0x128048 [0x45, 0x89, 0xCB] (fun s => s.RIP = 0x128048) (movR32R32Effect 0x128048 3 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x128048 3 11 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x128048 0x45 0xcb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12804b [0x46, 0x0F, 0xB6, 0x0C, 0x16] (LoadPre 0x12804b (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x12804b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12804b 5 9 (.sib 6 (some 10) 0 .none))
      [.gpr 6, .gpr 10] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x12804b 5 9 (.sib 6 (some 10) 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x12804b 0x46 (by decide) 1 (.sib 6 (some 10) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128050 [0x44, 0x89, 0xCB] (fun s => s.RIP = 0x128050) (movR32R32Effect 0x128050 3 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x128050 3 3 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x128050 0x44 0xcb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128053 [0x41, 0xC1, 0xE3, 0x07] (fun s => s.RIP = 0x128053) (shlR32Effect 0x128053 4 11 7)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x128053 4 11 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x128053 0x41 0xe3 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128057 [0x41, 0x83, 0xE1, 0x7F] (fun s => s.RIP = 0x128057) (andR32Imm8Effect 0x128057 4 9 0x7f)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x128057 4 9 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x128057 0x41 0xe1 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12805b [0x45, 0x09, 0xD9] (fun s => s.RIP = 0x12805b) (orR32R32Effect 0x12805b 3 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (orR32R32Effect_footprint 0x12805b 3 9 11).toInstrSpec (or_r32_r32_rex_effect_step 0x12805b 0x45 0xd9 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12805e [0x41, 0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12805e) (movR32Imm32Effect 0x12805e 6 10 0x2)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x12805e 6 10 0x2).toInstrSpec (mov_r32_imm32_rex_effect_step 0x12805e 0x41 0xba (by decide) (by decide) 0x2) pre_rip
  have f7 : InstrSpec 0x128064 [0x84, 0xDB] (fun s => s.RIP = 0x128064) (testR8R8Effect 0x128064 2 3 3)
      [.gpr 3, .gpr 3] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128064 2 3 3).toInstrSpec (test_r8_r8_effect_step 0x128064 0xdb (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12804b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128050) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128053) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128057) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 61), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12805b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12805e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128064) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128066) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel32_effect_step 0x128066 9 0xb4) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128048 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128048 :=
  Rest.liftedBlock (rest_l128048 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128048 x hx)

theorem rest_l12806c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12806c bytes_l12806c) (entryMap (live .l12806c))
      3 0x12806c bytes_l12806c b_l12806c := by
  have f0 : InstrSpec 0x12806c [0x4D, 0x8D, 0x50, 0x02] (fun s => s.RIP = 0x12806c) (leaR64Effect 0x12806c 10 (.base 8 (.d8 0x2)))
      [.gpr 8] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x12806c 10 (.base 8 (.d8 0x2))).toInstrSpec (lea_r64_effect_step 0x12806c 0x4d (by decide) 2 (.base 8 (.d8 0x2)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128070 [0x49, 0x39, 0xD2] (fun s => s.RIP = 0x128070) (cmpR64R64Effect 0x128070 10 2)
      [.gpr 10, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x128070 10 2).toInstrSpec (cmp_r64_r64_effect_step 0x128070 0x49 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128070) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128073) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x128073 3 0x127) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12806c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12806c :=
  Rest.liftedBlock (rest_l12806c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12806c x hx)

theorem rest_l128079 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128079 bytes_l128079) (entryMap (live .l128079))
      9 0x128079 bytes_l128079 b_l128079 := by
  have f0 : InstrSpec 0x128079 [0x45, 0x89, 0xCB] (fun s => s.RIP = 0x128079) (movR32R32Effect 0x128079 3 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x128079 3 11 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x128079 0x45 0xcb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12807c [0x46, 0x0F, 0xB6, 0x0C, 0x16] (LoadPre 0x12807c (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x12807c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12807c 5 9 (.sib 6 (some 10) 0 .none))
      [.gpr 6, .gpr 10] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x12807c 5 9 (.sib 6 (some 10) 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x12807c 0x46 (by decide) 1 (.sib 6 (some 10) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128081 [0x44, 0x89, 0xCB] (fun s => s.RIP = 0x128081) (movR32R32Effect 0x128081 3 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x128081 3 3 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x128081 0x44 0xcb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128084 [0x41, 0xC1, 0xE3, 0x07] (fun s => s.RIP = 0x128084) (shlR32Effect 0x128084 4 11 7)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x128084 4 11 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x128084 0x41 0xe3 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128088 [0x41, 0x83, 0xE1, 0x7F] (fun s => s.RIP = 0x128088) (andR32Imm8Effect 0x128088 4 9 0x7f)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x128088 4 9 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x128088 0x41 0xe1 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12808c [0x45, 0x09, 0xD9] (fun s => s.RIP = 0x12808c) (orR32R32Effect 0x12808c 3 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (orR32R32Effect_footprint 0x12808c 3 9 11).toInstrSpec (or_r32_r32_rex_effect_step 0x12808c 0x45 0xd9 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12808f [0x41, 0xBA, 0x03, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12808f) (movR32Imm32Effect 0x12808f 6 10 0x3)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x12808f 6 10 0x3).toInstrSpec (mov_r32_imm32_rex_effect_step 0x12808f 0x41 0xba (by decide) (by decide) 0x3) pre_rip
  have f7 : InstrSpec 0x128095 [0x84, 0xDB] (fun s => s.RIP = 0x128095) (testR8R8Effect 0x128095 2 3 3)
      [.gpr 3, .gpr 3] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128095 2 3 3).toInstrSpec (test_r8_r8_effect_step 0x128095 0xdb (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12807c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128081) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128084) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128088) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 61), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12808c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12808f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128095) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128097) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel32_effect_step 0x128097 9 0x83) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128079 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128079 :=
  Rest.liftedBlock (rest_l128079 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128079 x hx)

theorem rest_l12809d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12809d bytes_l12809d) (entryMap (live .l12809d))
      3 0x12809d bytes_l12809d b_l12809d := by
  have f0 : InstrSpec 0x12809d [0x4D, 0x8D, 0x50, 0x03] (fun s => s.RIP = 0x12809d) (leaR64Effect 0x12809d 10 (.base 8 (.d8 0x3)))
      [.gpr 8] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x12809d 10 (.base 8 (.d8 0x3))).toInstrSpec (lea_r64_effect_step 0x12809d 0x4d (by decide) 2 (.base 8 (.d8 0x3)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1280a1 [0x49, 0x39, 0xD2] (fun s => s.RIP = 0x1280a1) (cmpR64R64Effect 0x1280a1 10 2)
      [.gpr 10, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1280a1 10 2).toInstrSpec (cmp_r64_r64_effect_step 0x1280a1 0x49 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280a1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280a4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1280a4 3 0xf6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12809d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12809d :=
  Rest.liftedBlock (rest_l12809d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12809d x hx)

theorem rest_l1280aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1280aa bytes_l1280aa) (entryMap (live .l1280aa))
      9 0x1280aa bytes_l1280aa b_l1280aa := by
  have f0 : InstrSpec 0x1280aa [0x45, 0x89, 0xCB] (fun s => s.RIP = 0x1280aa) (movR32R32Effect 0x1280aa 3 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1280aa 3 11 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x1280aa 0x45 0xcb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1280ad [0x46, 0x0F, 0xB6, 0x0C, 0x16] (LoadPre 0x1280ad (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x1280ad + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1280ad 5 9 (.sib 6 (some 10) 0 .none))
      [.gpr 6, .gpr 10] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1280ad 5 9 (.sib 6 (some 10) 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1280ad 0x46 (by decide) 1 (.sib 6 (some 10) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1280b2 [0x44, 0x89, 0xCB] (fun s => s.RIP = 0x1280b2) (movR32R32Effect 0x1280b2 3 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x1280b2 3 3 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x1280b2 0x44 0xcb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1280b5 [0x41, 0xC1, 0xE3, 0x07] (fun s => s.RIP = 0x1280b5) (shlR32Effect 0x1280b5 4 11 7)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x1280b5 4 11 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1280b5 0x41 0xe3 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1280b9 [0x41, 0x83, 0xE1, 0x7F] (fun s => s.RIP = 0x1280b9) (andR32Imm8Effect 0x1280b9 4 9 0x7f)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1280b9 4 9 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x1280b9 0x41 0xe1 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1280bd [0x45, 0x09, 0xD9] (fun s => s.RIP = 0x1280bd) (orR32R32Effect 0x1280bd 3 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1280bd 3 9 11).toInstrSpec (or_r32_r32_rex_effect_step 0x1280bd 0x45 0xd9 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1280c0 [0x41, 0xBA, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1280c0) (movR32Imm32Effect 0x1280c0 6 10 0x4)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x1280c0 6 10 0x4).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1280c0 0x41 0xba (by decide) (by decide) 0x4) pre_rip
  have f7 : InstrSpec 0x1280c6 [0x84, 0xDB] (fun s => s.RIP = 0x1280c6) (testR8R8Effect 0x1280c6 2 3 3)
      [.gpr 3, .gpr 3] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1280c6 2 3 3).toInstrSpec (test_r8_r8_effect_step 0x1280c6 0xdb (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280ad) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280b5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280b9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 61), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280bd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280c0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280c6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280c8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel8_effect_step 0x1280c8 9 0x56) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1280aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1280aa :=
  Rest.liftedBlock (rest_l1280aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1280aa x hx)

theorem rest_l1280ca [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1280ca bytes_l1280ca) (entryMap (live .l1280ca))
      3 0x1280ca bytes_l1280ca b_l1280ca := by
  have f0 : InstrSpec 0x1280ca [0x4D, 0x8D, 0x50, 0x04] (fun s => s.RIP = 0x1280ca) (leaR64Effect 0x1280ca 10 (.base 8 (.d8 0x4)))
      [.gpr 8] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x1280ca 10 (.base 8 (.d8 0x4))).toInstrSpec (lea_r64_effect_step 0x1280ca 0x4d (by decide) 2 (.base 8 (.d8 0x4)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1280ce [0x49, 0x39, 0xD2] (fun s => s.RIP = 0x1280ce) (cmpR64R64Effect 0x1280ce 10 2)
      [.gpr 10, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1280ce 10 2).toInstrSpec (cmp_r64_r64_effect_step 0x1280ce 0x49 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280ce) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280d1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1280d1 3 0xc9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1280ca [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1280ca :=
  Rest.liftedBlock (rest_l1280ca code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1280ca x hx)

theorem rest_l1280d7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1280d7 bytes_l1280d7) (entryMap (live .l1280d7))
      9 0x1280d7 bytes_l1280d7 b_l1280d7 := by
  have f0 : InstrSpec 0x1280d7 [0x45, 0x89, 0xCB] (fun s => s.RIP = 0x1280d7) (movR32R32Effect 0x1280d7 3 11 9)
      [.gpr 9] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1280d7 3 11 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x1280d7 0x45 0xcb (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1280da [0x46, 0x0F, 0xB6, 0x0C, 0x16] (LoadPre 0x1280da (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x1280da + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1280da 5 9 (.sib 6 (some 10) 0 .none))
      [.gpr 6, .gpr 10] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x1280da 5 9 (.sib 6 (some 10) 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1280da 0x46 (by decide) 1 (.sib 6 (some 10) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1280df [0x44, 0x89, 0xCB] (fun s => s.RIP = 0x1280df) (movR32R32Effect 0x1280df 3 3 9)
      [.gpr 9] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x1280df 3 3 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x1280df 0x44 0xcb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1280e2 [0x41, 0xC1, 0xE3, 0x07] (fun s => s.RIP = 0x1280e2) (shlR32Effect 0x1280e2 4 11 7)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x1280e2 4 11 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1280e2 0x41 0xe3 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1280e6 [0x41, 0x83, 0xE1, 0x7F] (fun s => s.RIP = 0x1280e6) (andR32Imm8Effect 0x1280e6 4 9 0x7f)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1280e6 4 9 0x7f).toInstrSpec (and_r32_imm8_rex_effect_step 0x1280e6 0x41 0xe1 0x7f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1280ea [0x45, 0x09, 0xD9] (fun s => s.RIP = 0x1280ea) (orR32R32Effect 0x1280ea 3 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1280ea 3 9 11).toInstrSpec (or_r32_r32_rex_effect_step 0x1280ea 0x45 0xd9 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1280ed [0x41, 0xBA, 0x05, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1280ed) (movR32Imm32Effect 0x1280ed 6 10 0x5)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x1280ed 6 10 0x5).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1280ed 0x41 0xba (by decide) (by decide) 0x5) pre_rip
  have f7 : InstrSpec 0x1280f3 [0x84, 0xDB] (fun s => s.RIP = 0x1280f3) (testR8R8Effect 0x1280f3 2 3 3)
      [.gpr 3, .gpr 3] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1280f3 2 3 3).toInstrSpec (test_r8_r8_effect_step 0x1280f3 0xdb (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280da) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280e2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280e6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 61), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280ea) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280ed) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280f3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .SF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280f5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 69) (jcc_rel8_effect_step 0x1280f5 9 0x29) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1280d7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1280d7 :=
  Rest.liftedBlock (rest_l1280d7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1280d7 x hx)

theorem rest_l1280f7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1280f7 bytes_l1280f7) (entryMap (live .l1280f7))
      3 0x1280f7 bytes_l1280f7 b_l1280f7 := by
  have f0 : InstrSpec 0x1280f7 [0x4D, 0x8D, 0x50, 0x05] (fun s => s.RIP = 0x1280f7) (leaR64Effect 0x1280f7 10 (.base 8 (.d8 0x5)))
      [.gpr 8] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x1280f7 10 (.base 8 (.d8 0x5))).toInstrSpec (lea_r64_effect_step 0x1280f7 0x4d (by decide) 2 (.base 8 (.d8 0x5)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1280fb [0x49, 0x39, 0xD2] (fun s => s.RIP = 0x1280fb) (cmpR64R64Effect 0x1280fb 10 2)
      [.gpr 10, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1280fb 10 2).toInstrSpec (cmp_r64_r64_effect_step 0x1280fb 0x49 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280fb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1280fe) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1280fe 3 0x9c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1280f7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1280f7 :=
  Rest.liftedBlock (rest_l1280f7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1280f7 x hx)

theorem rest_l128104 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128104 bytes_l128104) (entryMap (live .l128104))
      3 0x128104 bytes_l128104 b_l128104 := by
  have f0 : InstrSpec 0x128104 [0x46, 0x0F, 0xB6, 0x14, 0x16] (LoadPre 0x128104 (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x128104 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x128104 5 10 (.sib 6 (some 10) 0 .none))
      [.gpr 6, .gpr 10] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x128104 5 10 (.sib 6 (some 10) 0 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x128104 0x46 (by decide) 2 (.sib 6 (some 10) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128109 [0x41, 0x83, 0xFA, 0x10] (fun s => s.RIP = 0x128109) (cmpR32Imm8Effect 0x128109 4 10 0x10)
      [.gpr 10] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x128109 4 10 0x10).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x128109 0x41 0xfa 0x10 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128109) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12810d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x12810d 3 0xa5) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128104 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128104 :=
  Rest.liftedBlock (rest_l128104 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128104 x hx)

theorem rest_l128113 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128113 bytes_l128113) (entryMap (live .l128113))
      3 0x128113 bytes_l128113 b_l128113 := by
  have f0 : InstrSpec 0x128113 [0x41, 0xC1, 0xE1, 0x07] (fun s => s.RIP = 0x128113) (shlR32Effect 0x128113 4 9 7)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR32Effect_footprint 0x128113 4 9 7).toInstrSpec (shl_r32_imm8_rex_effect_step 0x128113 0x41 0xe1 0x7 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128117 [0x45, 0x09, 0xD1] (fun s => s.RIP = 0x128117) (orR32R32Effect 0x128117 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (orR32R32Effect_footprint 0x128117 3 9 10).toInstrSpec (or_r32_r32_rex_effect_step 0x128117 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12811a [0x41, 0xBA, 0x06, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12811a) (movR32Imm32Effect 0x12811a 6 10 0x6)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x12811a 6 10 0x6).toInstrSpec (mov_r32_imm32_rex_effect_step 0x12811a 0x41 0xba (by decide) (by decide) 0x6) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128117) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12811a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 55), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128120) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 59) (by decide) rfl

theorem block_l128113 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128113 :=
  Rest.liftedBlock (rest_l128113 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128113 x hx)

theorem rest_l128120 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128120 bytes_l128120) (entryMap (live .l128120))
      4 0x128120 bytes_l128120 b_l128120 := by
  have f0 : InstrSpec 0x128120 [0x4D, 0x01, 0xD0] (fun s => s.RIP = 0x128120) (addR64R64Effect 0x128120 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x128120 8 10).toInstrSpec (add_r64_r64_effect_step 0x128120 0x4d 0xd0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128123 [0x49, 0xC1, 0xE1, 0x20] (fun s => s.RIP = 0x128123) (shlR64Effect 0x128123 4 9 32)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x128123 4 9 32).toInstrSpec (shl_r64_imm8_effect_step 0x128123 0x49 0xe1 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128127 [0x49, 0xFF, 0xC1] (fun s => s.RIP = 0x128127) (incR64Effect 0x128127 9)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (incR64Effect_footprint 0x128127 9).toInstrSpec (inc_r64_effect_step 0x128127 0x49 0xc1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128123) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 53), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128127) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 53), (9, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12812a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x12812a 0xfffffed7 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128120 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128120 :=
  Rest.liftedBlock (rest_l128120 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128120 x hx)

theorem rest_l128130 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128130 bytes_l128130) (entryMap (live .l128130))
      5 0x128130 bytes_l128130 b_l128130 := by
  have f0 : InstrSpec 0x128130 [0x0F, 0xB6, 0x3E] (LoadPre 0x128130 (fun s => AddrMode.addr (.base 6 .none) s (0x128130 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x128130 3 7 (.base 6 .none))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x128130 3 7 (.base 6 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x128130 7 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128133 [0x44, 0x69, 0xC7, 0xCD, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128133) (imulR32R32Imm32Effect 0x128133 7 8 7 0xcd)
      [.gpr 7] [] [.reg 8, .flags, .rip] :=
    (imulR32R32Imm32Effect_footprint 0x128133 7 8 7 0xcd).toInstrSpec (imul_r32_r32_imm32_rex_effect_step 0x128133 0x44 (by decide) 0xc7 (by decide) 0xcd) pre_rip
  have f2 : InstrSpec 0x12813a [0x41, 0xC1, 0xE8, 0x0D] (fun s => s.RIP = 0x12813a) (shrR32Effect 0x12813a 4 8 13)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x12813a 4 8 13).toInstrSpec (shr_r32_imm8_rex_effect_step 0x12813a 0x41 0xe8 0xd (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12813e [0x66, 0x83, 0xFF, 0x78] (fun s => s.RIP = 0x12813e) (cmpR16Imm8Effect 0x12813e 4 7 0x78)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpR16Imm8Effect_footprint 0x12813e 4 7 0x78).toInstrSpec (cmp_r16_imm8_effect_step 0x12813e 0xff 0x78 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128133) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12813a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12813e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128142) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x128142 3 0x4f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128130 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128130 :=
  Rest.liftedBlock (rest_l128130 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128130 x hx)

theorem rest_l128144 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128144 bytes_l128144) (entryMap (live .l128144))
      8 0x128144 bytes_l128144 b_l128144 := by
  have f0 : InstrSpec 0x128144 [0x41, 0xC1, 0xE0, 0x03] (fun s => s.RIP = 0x128144) (shlR32Effect 0x128144 4 8 3)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR32Effect_footprint 0x128144 4 8 3).toInstrSpec (shl_r32_imm8_rex_effect_step 0x128144 0x41 0xe0 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128148 [0x47, 0x8D, 0x04, 0x80] (fun s => s.RIP = 0x128148) (leaR32Effect 0x128148 4 8 (.sib 8 (some 8) 2 .none))
      [.gpr 8, .gpr 8] [] [.reg 8, .rip] :=
    (leaR32Effect_footprint 0x128148 4 8 (.sib 8 (some 8) 2 .none)).toInstrSpec (lea_r32_rex_effect_step 0x128148 0x47 (by decide) 0 (.sib 8 (some 8) 2 .none) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12814c [0x44, 0x28, 0xC7] (fun s => s.RIP = 0x12814c) (subR8R8Effect 0x12814c 3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (subR8R8Effect_footprint 0x12814c 3 7 8).toInstrSpec (sub_r8_r8_rex_effect_step 0x12814c 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12814f [0x44, 0x0F, 0xB6, 0xCF] (fun s => s.RIP = 0x12814f) (movzxR32R8Effect 0x12814f 4 9 7)
      [.gpr 7] [] [.reg 9, .rip] :=
    (movzxR32R8Effect_footprint 0x12814f 4 9 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12814f 0x44 (by decide) 0xcf (by decide)) pre_rip
  have f4 : InstrSpec 0x128153 [0x49, 0xC1, 0xE1, 0x20] (fun s => s.RIP = 0x128153) (shlR64Effect 0x128153 4 9 32)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR64Effect_footprint 0x128153 4 9 32).toInstrSpec (shl_r64_imm8_effect_step 0x128153 0x49 0xe1 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x128157 [0x49, 0xFF, 0xC1] (fun s => s.RIP = 0x128157) (incR64Effect 0x128157 9)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (incR64Effect_footprint 0x128157 9).toInstrSpec (inc_r64_effect_step 0x128157 0x49 0xc1 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12815a [0x41, 0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12815a) (movR32Imm32Effect 0x12815a 6 8 0x1)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x12815a 6 8 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x12815a 0x41 0xb8 (by decide) (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128148) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12814c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12814f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 55), (9, 59), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128153) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 55), (9, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128157) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12815a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 65), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128160) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 67) (jmp_rel32_effect_step 0x128160 0xfffffea1 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128144 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128144 :=
  Rest.liftedBlock (rest_l128144 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128144 x hx)

theorem rest_l128165 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128165 bytes_l128165) (entryMap (live .l128165))
      5 0x128165 bytes_l128165 b_l128165 := by
  have f0 : InstrSpec 0x128165 [0xBF, 0x04, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128165) (movR32Imm32Effect 0x128165 5 7 0x4)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x128165 5 7 0x4).toInstrSpec (mov_r32_imm32_effect_step 0x128165 0xbf (by decide) 0x4) pre_rip
  have f1 : InstrSpec 0x12816a [0x48, 0x89, 0x78, 0x08] (StorePre 0x12816a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x12816a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12816a 7 (.base 0 (.d8 0x8)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x12816a 7 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12816a 0x48 (by decide) 7 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x12816e [0x48, 0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x12816e 7 (fun s => AddrMode.addr (.base 0 .none) s (0x12816e + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x12816e (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x12816e (.base 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x12816e 0x48 (by decide) (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x128175 [0x5B] (PopPre 0x128175) (popR64Effect 0x128175 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128175 1 3).toInstrSpec (pop_r64_effect_step 0x128175 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128176 [0xC3] (RetPre 0x128176) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128176).toInstrSpec (ret_effect_step 0x128176) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12816a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12816e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128175) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128176) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l128165 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128165 :=
  Rest.liftedBlock (rest_l128165 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128165 x hx)

theorem rest_l128177 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128177 bytes_l128177) (entryMap (live .l128177))
      1 0x128177 bytes_l128177 b_l128177 := by
  have f0 : InstrSpec 0x128177 [0xC1, 0xE1, 0x08] (fun s => s.RIP = 0x128177) (shlR32Effect 0x128177 3 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x128177 3 1 8).toInstrSpec (shl_r32_imm8_effect_step 0x128177 0xe1 0x8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12817a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l128177 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128177 :=
  Rest.liftedBlock (rest_l128177 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128177 x hx)

theorem rest_l12817a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12817a bytes_l12817a) (entryMap (live .l12817a))
      5 0x12817a bytes_l12817a b_l12817a := by
  have f0 : InstrSpec 0x12817a [0x48, 0x09, 0xCF] (fun s => s.RIP = 0x12817a) (orR64R64Effect 0x12817a 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x12817a 7 1).toInstrSpec (or_r64_r64_effect_step 0x12817a 0x48 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12817d [0x48, 0x89, 0x78, 0x08] (StorePre 0x12817d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x12817d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12817d 7 (.base 0 (.d8 0x8)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x12817d 7 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12817d 0x48 (by decide) 7 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x128181 [0x48, 0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x128181 7 (fun s => AddrMode.addr (.base 0 .none) s (0x128181 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x128181 (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x128181 (.base 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x128181 0x48 (by decide) (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x128188 [0x5B] (PopPre 0x128188) (popR64Effect 0x128188 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128188 1 3).toInstrSpec (pop_r64_effect_step 0x128188 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128189 [0xC3] (RetPre 0x128189) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128189).toInstrSpec (ret_effect_step 0x128189) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12817d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128181) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128188) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 58), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128189) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f4 (by decide) rfl rfl rfl (by decide)

theorem block_l12817a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12817a :=
  Rest.liftedBlock (rest_l12817a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12817a x hx)

theorem rest_l12818a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12818a bytes_l12818a) (entryMap (live .l12818a))
      4 0x12818a bytes_l12818a b_l12818a := by
  have f0 : InstrSpec 0x12818a [0x48, 0x89, 0x30] (StorePre 0x12818a 3 (fun s => AddrMode.addr (.base 0 .none) s (0x12818a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12818a 6 (.base 0 .none))
      [.gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x12818a 6 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x12818a 0x48 (by decide) 6 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x12818d [0x48, 0x89, 0x50, 0x08] (StorePre 0x12818d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x12818d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12818d 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x12818d 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x12818d 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x128191 [0x5B] (PopPre 0x128191) (popR64Effect 0x128191 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128191 1 3).toInstrSpec (pop_r64_effect_step 0x128191 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128192 [0xC3] (RetPre 0x128192) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128192).toInstrSpec (ret_effect_step 0x128192) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12818d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128191) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128192) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l12818a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12818a :=
  Rest.liftedBlock (rest_l12818a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12818a x hx)

theorem rest_l128193 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128193 bytes_l128193) (entryMap (live .l128193))
      4 0x128193 bytes_l128193 b_l128193 := by
  have f0 : InstrSpec 0x128193 [0x41, 0x0F, 0xB6, 0xC8] (fun s => s.RIP = 0x128193) (movzxR32R8Effect 0x128193 4 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x128193 4 1 8).toInstrSpec (movzx_r32_r8_rex_effect_step 0x128193 0x41 (by decide) 0xc8 (by decide)) pre_rip
  have f1 : InstrSpec 0x128197 [0x48, 0xC1, 0xE1, 0x20] (fun s => s.RIP = 0x128197) (shlR64Effect 0x128197 4 1 32)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x128197 4 1 32).toInstrSpec (shl_r64_imm8_effect_step 0x128197 0x48 0xe1 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12819b [0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x12819b) (shlR32Effect 0x12819b 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x12819b 3 7 8).toInstrSpec (shl_r32_imm8_effect_step 0x12819b 0xe7 0x8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128197) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12819b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12819e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x12819e 0xda (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128193 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128193 :=
  Rest.liftedBlock (rest_l128193 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128193 x hx)

theorem rest_l1281a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1281a0 bytes_l1281a0) (entryMap (live .l1281a0))
      6 0x1281a0 bytes_l1281a0 b_l1281a0 := by
  have f0 : InstrSpec 0x1281a0 [0x48, 0x81, 0xE7, 0x00, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x1281a0) (andR64Imm32Effect 0x1281a0 7 0xffffff00)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR64Imm32Effect_footprint 0x1281a0 7 0xffffff00).toInstrSpec (and_r64_imm32_effect_step 0x1281a0 0x48 0xe7 0xffffff00 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1281a7 [0x48, 0x83, 0xCF, 0x02] (fun s => s.RIP = 0x1281a7) (orR64Imm8Effect 0x1281a7 7 0x2)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (orR64Imm8Effect_footprint 0x1281a7 7 0x2).toInstrSpec (or_r64_imm8_effect_step 0x1281a7 0x48 0xcf 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1281ab [0x48, 0x89, 0x78, 0x08] (StorePre 0x1281ab 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1281ab + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1281ab 7 (.base 0 (.d8 0x8)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1281ab 7 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1281ab 0x48 (by decide) 7 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1281af [0x48, 0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1281af 7 (fun s => AddrMode.addr (.base 0 .none) s (0x1281af + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x1281af (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1281af (.base 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1281af 0x48 (by decide) (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1281b6 [0x5B] (PopPre 0x1281b6) (popR64Effect 0x1281b6 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1281b6 1 3).toInstrSpec (pop_r64_effect_step 0x1281b6 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1281b7 [0xC3] (RetPre 0x1281b7) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1281b7).toInstrSpec (ret_effect_step 0x1281b7) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281a7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281ab) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281af) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281b6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 60), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281b7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 63), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l1281a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1281a0 :=
  Rest.liftedBlock (rest_l1281a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1281a0 x hx)

theorem rest_l1281b8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1281b8 bytes_l1281b8) (entryMap (live .l1281b8))
      6 0x1281b8 bytes_l1281b8 b_l1281b8 := by
  have f0 : InstrSpec 0x1281b8 [0x48, 0x81, 0xE7, 0x00, 0xFF, 0xFF, 0xFF] (fun s => s.RIP = 0x1281b8) (andR64Imm32Effect 0x1281b8 7 0xffffff00)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR64Imm32Effect_footprint 0x1281b8 7 0xffffff00).toInstrSpec (and_r64_imm32_effect_step 0x1281b8 0x48 0xe7 0xffffff00 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1281bf [0x48, 0xFF, 0xC7] (fun s => s.RIP = 0x1281bf) (incR64Effect 0x1281bf 7)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (incR64Effect_footprint 0x1281bf 7).toInstrSpec (inc_r64_effect_step 0x1281bf 0x48 0xc7 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1281c2 [0x48, 0x89, 0x78, 0x08] (StorePre 0x1281c2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1281c2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1281c2 7 (.base 0 (.d8 0x8)))
      [.gpr 7, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1281c2 7 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1281c2 0x48 (by decide) 7 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1281c6 [0x48, 0xC7, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1281c6 7 (fun s => AddrMode.addr (.base 0 .none) s (0x1281c6 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x1281c6 (.base 0 .none) 0x0)
      [.gpr 0] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1281c6 (.base 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1281c6 0x48 (by decide) (.base 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1281cd [0x5B] (PopPre 0x1281cd) (popR64Effect 0x1281cd 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1281cd 1 3).toInstrSpec (pop_r64_effect_step 0x1281cd 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1281ce [0xC3] (RetPre 0x1281ce) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1281ce).toInstrSpec (ret_effect_step 0x1281ce) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281bf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281c2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281c6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281cd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 60), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1281ce) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 59), (4, 63), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f5 (by decide) rfl rfl rfl (by decide)

theorem block_l1281b8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1281b8 :=
  Rest.liftedBlock (rest_l1281b8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1281b8 x hx)

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

theorem_by block_l127fc0_eval :
    program.runBlock (dialect code) ⟨.l127fc0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127fcd_eval :
    program.runBlock (dialect code) ⟨.l127fcd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l127fe7_eval :
    program.runBlock (dialect code) ⟨.l127fe7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128000_eval :
    program.runBlock (dialect code) ⟨.l128000, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128006_eval :
    program.runBlock (dialect code) ⟨.l128006, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128012_eval :
    program.runBlock (dialect code) ⟨.l128012, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12801b_eval :
    program.runBlock (dialect code) ⟨.l12801b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128020_eval :
    program.runBlock (dialect code) ⟨.l128020, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12803b_eval :
    program.runBlock (dialect code) ⟨.l12803b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128048_eval :
    program.runBlock (dialect code) ⟨.l128048, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12806c_eval :
    program.runBlock (dialect code) ⟨.l12806c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128079_eval :
    program.runBlock (dialect code) ⟨.l128079, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12809d_eval :
    program.runBlock (dialect code) ⟨.l12809d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1280aa_eval :
    program.runBlock (dialect code) ⟨.l1280aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1280ca_eval :
    program.runBlock (dialect code) ⟨.l1280ca, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1280d7_eval :
    program.runBlock (dialect code) ⟨.l1280d7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1280f7_eval :
    program.runBlock (dialect code) ⟨.l1280f7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128104_eval :
    program.runBlock (dialect code) ⟨.l128104, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128113_eval :
    program.runBlock (dialect code) ⟨.l128113, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128120_eval :
    program.runBlock (dialect code) ⟨.l128120, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128130_eval :
    program.runBlock (dialect code) ⟨.l128130, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128144_eval :
    program.runBlock (dialect code) ⟨.l128144, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128165_eval :
    program.runBlock (dialect code) ⟨.l128165, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128177_eval :
    program.runBlock (dialect code) ⟨.l128177, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12817a_eval :
    program.runBlock (dialect code) ⟨.l12817a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12818a_eval :
    program.runBlock (dialect code) ⟨.l12818a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128193_eval :
    program.runBlock (dialect code) ⟨.l128193, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1281a0_eval :
    program.runBlock (dialect code) ⟨.l1281a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1281b8_eval :
    program.runBlock (dialect code) ⟨.l1281b8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
