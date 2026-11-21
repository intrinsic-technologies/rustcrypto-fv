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

theorem rest_l12a850 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a850 bytes_l12a850) (entryMap (live .l12a850))
      5 0x12a850 bytes_l12a850 b_l12a850 := by
  have f0 : InstrSpec 0x12a850 [0x41, 0x89, 0xC9] (fun s => s.RIP = 0x12a850) (movR32R32Effect 0x12a850 3 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x12a850 3 9 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x12a850 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a853 [0x41, 0x83, 0xE1, 0x18] (fun s => s.RIP = 0x12a853) (andR32Imm8Effect 0x12a853 4 9 0x18)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a853 4 9 0x18).toInstrSpec (and_r32_imm8_rex_effect_step 0x12a853 0x41 0xe1 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a857 [0x4E, 0x8D, 0x04, 0x0E] (fun s => s.RIP = 0x12a857) (leaR64Effect 0x12a857 8 (.sib 6 (some 9) 0 .none))
      [.gpr 6, .gpr 9] [] [.reg 8, .rip] :=
    (leaR64Effect_footprint 0x12a857 8 (.sib 6 (some 9) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a857 0x4e (by decide) 0 (.sib 6 (some 9) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a85b [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x12a85b) (testR64R64Effect 0x12a85b 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12a85b 9 9).toInstrSpec (test_r64_r64_effect_step 0x12a85b 0x4d 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a853) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a857) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a85b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a85e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x12a85e 4 0x30) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a850 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a850 :=
  Rest.liftedBlock (rest_l12a850 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a850 x hx)

theorem rest_l12a860 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a860 bytes_l12a860) (entryMap (live .l12a860))
      3 0x12a860 bytes_l12a860 b_l12a860 := by
  have f0 : InstrSpec 0x12a860 [0x4E, 0x8D, 0x14, 0x0A] (fun s => s.RIP = 0x12a860) (leaR64Effect 0x12a860 10 (.sib 2 (some 9) 0 .none))
      [.gpr 2, .gpr 9] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x12a860 10 (.sib 2 (some 9) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a860 0x4e (by decide) 2 (.sib 2 (some 9) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a864 [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x12a864) (xorR32R32Effect 0x12a864 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a864 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x12a864 0x45 0xdb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a867 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a867) (fun _ => nopEffect 0x12a867 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12a867 9).toInstrSpec (nop_m_effect_step 0x12a867 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a864) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a867) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a870) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l12a860 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a860 :=
  Rest.liftedBlock (rest_l12a860 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a860 x hx)

theorem rest_l12a870 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a870 bytes_l12a870) (entryMap (live .l12a870))
      4 0x12a870 bytes_l12a870 b_l12a870 := by
  have f0 : InstrSpec 0x12a870 [0x4A, 0x8B, 0x04, 0x1E] (LoadPre 0x12a870 (fun s => AddrMode.addr (.sib 6 (some 11) 0 .none) s (0x12a870 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a870 0 (.sib 6 (some 11) 0 .none))
      [.gpr 6, .gpr 11] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12a870 0 (.sib 6 (some 11) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a870 0x4a (by decide) 0 (.sib 6 (some 11) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a874 [0x4A, 0x8B, 0x3C, 0x1A] (LoadPre 0x12a874 (fun s => AddrMode.addr (.sib 2 (some 11) 0 .none) s (0x12a874 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a874 7 (.sib 2 (some 11) 0 .none))
      [.gpr 2, .gpr 11] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12a874 7 (.sib 2 (some 11) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12a874 0x4a (by decide) 7 (.sib 2 (some 11) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a878 [0x48, 0x39, 0xF8] (fun s => s.RIP = 0x12a878) (cmpR64R64Effect 0x12a878 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a878 0 7).toInstrSpec (cmp_r64_r64_effect_step 0x12a878 0x48 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a874) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a878) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a87b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x12a87b 5 0xad) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a870 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a870 :=
  Rest.liftedBlock (rest_l12a870 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a870 x hx)

theorem rest_l12a881 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a881 bytes_l12a881) (entryMap (live .l12a881))
      3 0x12a881 bytes_l12a881 b_l12a881 := by
  have f0 : InstrSpec 0x12a881 [0x49, 0x83, 0xC3, 0x08] (fun s => s.RIP = 0x12a881) (addR64Imm8Effect 0x12a881 11 0x8)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a881 11 0x8).toInstrSpec (add_r64_imm8_effect_step 0x12a881 0x49 0xc3 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a885 [0x4D, 0x39, 0xD9] (fun s => s.RIP = 0x12a885) (cmpR64R64Effect 0x12a885 9 11)
      [.gpr 9, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a885 9 11).toInstrSpec (cmp_r64_r64_effect_step 0x12a885 0x4d 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a885) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a888) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12a888 5 0xe6) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a881 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a881 :=
  Rest.liftedBlock (rest_l12a881 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a881 x hx)

theorem rest_l12a88a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a88a bytes_l12a88a) (entryMap (live .l12a88a))
      2 0x12a88a bytes_l12a88a b_l12a88a := by
  have f0 : InstrSpec 0x12a88a [0x4C, 0x89, 0xD2] (fun s => s.RIP = 0x12a88a) (movR64R64Effect 0x12a88a 2 10)
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a88a 2 10).toInstrSpec (mov_r64_r64_effect_step 0x12a88a 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a88d [0x4C, 0x89, 0xC6] (fun s => s.RIP = 0x12a88d) (movR64R64Effect 0x12a88d 6 8)
      [.gpr 8] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12a88d 6 8).toInstrSpec (mov_r64_r64_effect_step 0x12a88d 0x4c 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a88d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a890) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l12a88a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a88a :=
  Rest.liftedBlock (rest_l12a88a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a88a x hx)

theorem rest_l12a890 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a890 bytes_l12a890) (entryMap (live .l12a890))
      5 0x12a890 bytes_l12a890 b_l12a890 := by
  have f0 : InstrSpec 0x12a890 [0x41, 0x89, 0xC9] (fun s => s.RIP = 0x12a890) (movR32R32Effect 0x12a890 3 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x12a890 3 9 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x12a890 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a893 [0x41, 0x83, 0xE1, 0x04] (fun s => s.RIP = 0x12a893) (andR32Imm8Effect 0x12a893 4 9 0x4)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a893 4 9 0x4).toInstrSpec (and_r32_imm8_rex_effect_step 0x12a893 0x41 0xe1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a897 [0x4A, 0x8D, 0x04, 0x0E] (fun s => s.RIP = 0x12a897) (leaR64Effect 0x12a897 0 (.sib 6 (some 9) 0 .none))
      [.gpr 6, .gpr 9] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x12a897 0 (.sib 6 (some 9) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a897 0x4a (by decide) 0 (.sib 6 (some 9) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a89b [0x4D, 0x85, 0xC9] (fun s => s.RIP = 0x12a89b) (testR64R64Effect 0x12a89b 9 9)
      [.gpr 9, .gpr 9] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12a89b 9 9).toInstrSpec (test_r64_r64_effect_step 0x12a89b 0x4d 0xc9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a893) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a897) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a89b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a89e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x12a89e 4 0x2f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a890 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a890 :=
  Rest.liftedBlock (rest_l12a890 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a890 x hx)

theorem rest_l12a8a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a8a0 bytes_l12a8a0) (entryMap (live .l12a8a0))
      3 0x12a8a0 bytes_l12a8a0 b_l12a8a0 := by
  have f0 : InstrSpec 0x12a8a0 [0x4E, 0x8D, 0x14, 0x0A] (fun s => s.RIP = 0x12a8a0) (leaR64Effect 0x12a8a0 10 (.sib 2 (some 9) 0 .none))
      [.gpr 2, .gpr 9] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x12a8a0 10 (.sib 2 (some 9) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a8a0 0x4e (by decide) 2 (.sib 2 (some 9) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a8a4 [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x12a8a4) (xorR32R32Effect 0x12a8a4 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a8a4 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x12a8a4 0x45 0xdb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a8a7 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a8a7) (fun _ => nopEffect 0x12a8a7 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12a8a7 9).toInstrSpec (nop_m_effect_step 0x12a8a7 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8a7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 53), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8b0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l12a8a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a8a0 :=
  Rest.liftedBlock (rest_l12a8a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a8a0 x hx)

theorem rest_l12a8b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a8b0 bytes_l12a8b0) (entryMap (live .l12a8b0))
      4 0x12a8b0 bytes_l12a8b0 b_l12a8b0 := by
  have f0 : InstrSpec 0x12a8b0 [0x43, 0x8B, 0x34, 0x18] (LoadPre 0x12a8b0 (fun s => AddrMode.addr (.sib 8 (some 11) 0 .none) s (0x12a8b0 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12a8b0 6 (.sib 8 (some 11) 0 .none))
      [.gpr 8, .gpr 11] [] [.reg 6, .rip] :=
    (movR32M32Effect_footprint 0x12a8b0 6 (.sib 8 (some 11) 0 .none)).toInstrSpec (mov_r32_m32_effect_step 0x12a8b0 0x43 (by decide) 6 (.sib 8 (some 11) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a8b4 [0x42, 0x8B, 0x3C, 0x1A] (LoadPre 0x12a8b4 (fun s => AddrMode.addr (.sib 2 (some 11) 0 .none) s (0x12a8b4 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12a8b4 7 (.sib 2 (some 11) 0 .none))
      [.gpr 2, .gpr 11] [] [.reg 7, .rip] :=
    (movR32M32Effect_footprint 0x12a8b4 7 (.sib 2 (some 11) 0 .none)).toInstrSpec (mov_r32_m32_effect_step 0x12a8b4 0x42 (by decide) 7 (.sib 2 (some 11) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a8b8 [0x39, 0xFE] (fun s => s.RIP = 0x12a8b8) (cmpR32R32Effect 0x12a8b8 2 6 7)
      [.gpr 6, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x12a8b8 2 6 7).toInstrSpec (cmp_r32_r32_effect_step 0x12a8b8 0xfe (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8b4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8b8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8ba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x12a8ba 5 0xad) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a8b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a8b0 :=
  Rest.liftedBlock (rest_l12a8b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a8b0 x hx)

theorem rest_l12a8c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a8c0 bytes_l12a8c0) (entryMap (live .l12a8c0))
      3 0x12a8c0 bytes_l12a8c0 b_l12a8c0 := by
  have f0 : InstrSpec 0x12a8c0 [0x49, 0x83, 0xC3, 0x04] (fun s => s.RIP = 0x12a8c0) (addR64Imm8Effect 0x12a8c0 11 0x4)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a8c0 11 0x4).toInstrSpec (add_r64_imm8_effect_step 0x12a8c0 0x49 0xc3 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a8c4 [0x4D, 0x39, 0xD9] (fun s => s.RIP = 0x12a8c4) (cmpR64R64Effect 0x12a8c4 9 11)
      [.gpr 9, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a8c4 9 11).toInstrSpec (cmp_r64_r64_effect_step 0x12a8c4 0x4d 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8c7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12a8c7 5 0xe7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a8c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a8c0 :=
  Rest.liftedBlock (rest_l12a8c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a8c0 x hx)

theorem rest_l12a8c9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a8c9 bytes_l12a8c9) (entryMap (live .l12a8c9))
      2 0x12a8c9 bytes_l12a8c9 b_l12a8c9 := by
  have f0 : InstrSpec 0x12a8c9 [0x4C, 0x89, 0xD2] (fun s => s.RIP = 0x12a8c9) (movR64R64Effect 0x12a8c9 2 10)
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a8c9 2 10).toInstrSpec (mov_r64_r64_effect_step 0x12a8c9 0x4c 0xd2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a8cc [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x12a8cc) (movR64R64Effect 0x12a8cc 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12a8cc 6 0).toInstrSpec (mov_r64_r64_effect_step 0x12a8cc 0x48 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8cc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8cf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l12a8c9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a8c9 :=
  Rest.liftedBlock (rest_l12a8c9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a8c9 x hx)

theorem rest_l12a8cf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a8cf bytes_l12a8cf) (entryMap (live .l12a8cf))
      3 0x12a8cf bytes_l12a8cf b_l12a8cf := by
  have f0 : InstrSpec 0x12a8cf [0x41, 0x89, 0xC9] (fun s => s.RIP = 0x12a8cf) (movR32R32Effect 0x12a8cf 3 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x12a8cf 3 9 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x12a8cf 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a8d2 [0x41, 0x83, 0xE1, 0x02] (fun s => s.RIP = 0x12a8d2) (andR32Imm8Effect 0x12a8d2 4 9 0x2)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x12a8d2 4 9 0x2).toInstrSpec (and_r32_imm8_rex_effect_step 0x12a8d2 0x41 0xe1 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8d2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8d6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x12a8d6 4 0x38) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a8cf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a8cf :=
  Rest.liftedBlock (rest_l12a8cf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a8cf x hx)

theorem rest_l12a8d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a8d8 bytes_l12a8d8) (entryMap (live .l12a8d8))
      4 0x12a8d8 bytes_l12a8d8 b_l12a8d8 := by
  have f0 : InstrSpec 0x12a8d8 [0x4C, 0x01, 0xCE] (fun s => s.RIP = 0x12a8d8) (addR64R64Effect 0x12a8d8 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x12a8d8 6 9).toInstrSpec (add_r64_r64_effect_step 0x12a8d8 0x4c 0xce (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a8db [0x4E, 0x8D, 0x14, 0x0A] (fun s => s.RIP = 0x12a8db) (leaR64Effect 0x12a8db 10 (.sib 2 (some 9) 0 .none))
      [.gpr 2, .gpr 9] [] [.reg 10, .rip] :=
    (leaR64Effect_footprint 0x12a8db 10 (.sib 2 (some 9) 0 .none)).toInstrSpec (lea_r64_effect_step 0x12a8db 0x4e (by decide) 2 (.sib 2 (some 9) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a8df [0x45, 0x31, 0xDB] (fun s => s.RIP = 0x12a8df) (xorR32R32Effect 0x12a8df 3 11 11)
      [.gpr 11, .gpr 11] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a8df 3 11 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x12a8df 0x45 0xdb (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x12a8e2 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12a8e2) (fun _ => nopEffect 0x12a8e2 14)
      [] [] [.rip] :=
    (nopEffect_footprint 0x12a8e2 14).toInstrSpec (nop_m_effect_step 0x12a8e2 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8db) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8df) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 55), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8e2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (9, 9), (10, 55), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8f0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l12a8d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a8d8 :=
  Rest.liftedBlock (rest_l12a8d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a8d8 x hx)

theorem rest_l12a8f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a8f0 bytes_l12a8f0) (entryMap (live .l12a8f0))
      4 0x12a8f0 bytes_l12a8f0 b_l12a8f0 := by
  have f0 : InstrSpec 0x12a8f0 [0x46, 0x0F, 0xB7, 0x04, 0x18] (LoadPre 0x12a8f0 (fun s => AddrMode.addr (.sib 0 (some 11) 0 .none) s (0x12a8f0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x12a8f0 5 8 (.sib 0 (some 11) 0 .none))
      [.gpr 0, .gpr 11] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x12a8f0 5 8 (.sib 0 (some 11) 0 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x12a8f0 0x46 (by decide) 0 (.sib 0 (some 11) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a8f5 [0x42, 0x0F, 0xB7, 0x3C, 0x1A] (LoadPre 0x12a8f5 (fun s => AddrMode.addr (.sib 2 (some 11) 0 .none) s (0x12a8f5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x12a8f5 5 7 (.sib 2 (some 11) 0 .none))
      [.gpr 2, .gpr 11] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x12a8f5 5 7 (.sib 2 (some 11) 0 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x12a8f5 0x42 (by decide) 7 (.sib 2 (some 11) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a8fa [0x66, 0x41, 0x39, 0xF8] (fun s => s.RIP = 0x12a8fa) (cmpR16R16Effect 0x12a8fa 4 8 7)
      [.gpr 8, .gpr 7] [] [.flags, .rip] :=
    (cmpR16R16Effect_footprint 0x12a8fa 4 8 7).toInstrSpec (cmp_r16_r16_rex_effect_step 0x12a8fa 0x41 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a8fe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x12a8fe 5 0x94) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a8f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a8f0 :=
  Rest.liftedBlock (rest_l12a8f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a8f0 x hx)

theorem rest_l12a904 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a904 bytes_l12a904) (entryMap (live .l12a904))
      3 0x12a904 bytes_l12a904 b_l12a904 := by
  have f0 : InstrSpec 0x12a904 [0x49, 0x83, 0xC3, 0x02] (fun s => s.RIP = 0x12a904) (addR64Imm8Effect 0x12a904 11 0x2)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12a904 11 0x2).toInstrSpec (add_r64_imm8_effect_step 0x12a904 0x49 0xc3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a908 [0x4D, 0x39, 0xD9] (fun s => s.RIP = 0x12a908) (cmpR64R64Effect 0x12a908 9 11)
      [.gpr 9, .gpr 11] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a908 9 11).toInstrSpec (cmp_r64_r64_effect_step 0x12a908 0x4d 0xd9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a908) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a90b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x12a90b 5 0xe3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a904 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a904 :=
  Rest.liftedBlock (rest_l12a904 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a904 x hx)

theorem rest_l12a90d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a90d bytes_l12a90d) (entryMap (live .l12a90d))
      1 0x12a90d bytes_l12a90d b_l12a90d := by
  have f0 : InstrSpec 0x12a90d [0x4C, 0x89, 0xD2] (fun s => s.RIP = 0x12a90d) (movR64R64Effect 0x12a90d 2 10)
      [.gpr 10] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x12a90d 2 10).toInstrSpec (mov_r64_r64_effect_step 0x12a90d 0x4c 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a910) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l12a90d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a90d :=
  Rest.liftedBlock (rest_l12a90d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a90d x hx)

theorem rest_l12a910 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a910 bytes_l12a910) (entryMap (live .l12a910))
      3 0x12a910 bytes_l12a910 b_l12a910 := by
  have f0 : InstrSpec 0x12a910 [0x31, 0xC0] (fun s => s.RIP = 0x12a910) (xorR32R32Effect 0x12a910 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a910 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12a910 0xc0 (by decide)) pre_rip
  have f1 : InstrSpec 0x12a912 [0xF6, 0xC1, 0x01] (fun s => s.RIP = 0x12a912) (testR8Imm8LowEffect 0x12a912 1 0x1)
      [.gpr 1] [] [.flags, .rip] :=
    (testR8Imm8LowEffect_footprint 0x12a912 1 0x1).toInstrSpec (test_r8_imm8_low_effect_step 0x12a912 0xc1 0x1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a912) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a915) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x12a915 4 0xa3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a910 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a910 :=
  Rest.liftedBlock (rest_l12a910 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a910 x hx)

theorem rest_l12a91b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a91b bytes_l12a91b) (entryMap (live .l12a91b))
      4 0x12a91b bytes_l12a91b b_l12a91b := by
  have f0 : InstrSpec 0x12a91b [0x0F, 0xB6, 0x0E] (LoadPre 0x12a91b (fun s => AddrMode.addr (.base 6 .none) s (0x12a91b + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x12a91b 3 1 (.base 6 .none))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x12a91b 3 1 (.base 6 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x12a91b 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12a91e [0x0F, 0xB6, 0x12] (LoadPre 0x12a91e (fun s => AddrMode.addr (.base 2 .none) s (0x12a91e + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x12a91e 3 2 (.base 2 .none))
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x12a91e 3 2 (.base 2 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x12a91e 2 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12a921 [0x38, 0xD1] (fun s => s.RIP = 0x12a921) (cmpR8R8Effect 0x12a921 2 1 2)
      [.gpr 1, .gpr 2] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x12a921 2 1 2).toInstrSpec (cmp_r8_r8_effect_step 0x12a921 0xd1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a91e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a921) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a923) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x12a923 4 0x95) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a91b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a91b :=
  Rest.liftedBlock (rest_l12a91b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a91b x hx)

theorem rest_l12a929 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a929 bytes_l12a929) (entryMap (live .l12a929))
      3 0x12a929 bytes_l12a929 b_l12a929 := by
  have f0 : InstrSpec 0x12a929 [0x29, 0xD1] (fun s => s.RIP = 0x12a929) (subR32R32Effect 0x12a929 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a929 2 1 2).toInstrSpec (sub_r32_r32_effect_step 0x12a929 0xd1 (by decide)) pre_rip
  have f1 : InstrSpec 0x12a92b [0x89, 0xC8] (fun s => s.RIP = 0x12a92b) (movR32R32Effect 0x12a92b 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x12a92b 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x12a92b 0xc8 (by decide)) pre_rip
  have f2 : InstrSpec 0x12a92d [0xC3] (RetPre 0x12a92d) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a92d).toInstrSpec (ret_effect_step 0x12a92d) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a92b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a92d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 59) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f2 (by decide) rfl rfl rfl (by decide)

theorem block_l12a929 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a929 :=
  Rest.liftedBlock (rest_l12a929 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a929 x hx)

theorem rest_l12a92e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a92e bytes_l12a92e) (entryMap (live .l12a92e))
      2 0x12a92e bytes_l12a92e b_l12a92e := by
  have f0 : InstrSpec 0x12a92e [0x39, 0xF8] (fun s => s.RIP = 0x12a92e) (cmpR32R32Effect 0x12a92e 2 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x12a92e 2 0 7).toInstrSpec (cmp_r32_r32_effect_step 0x12a92e 0xf8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a930) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a930 5 0xd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a92e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a92e :=
  Rest.liftedBlock (rest_l12a92e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a92e x hx)

theorem rest_l12a932 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a932 bytes_l12a932) (entryMap (live .l12a932))
      4 0x12a932 bytes_l12a932 b_l12a932 := by
  have f0 : InstrSpec 0x12a932 [0x48, 0xC1, 0xEF, 0x20] (fun s => s.RIP = 0x12a932) (shrR64Effect 0x12a932 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a932 4 7 32).toInstrSpec (shr_r64_imm8_effect_step 0x12a932 0x48 0xef 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a936 [0x48, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x12a936) (shrR64Effect 0x12a936 4 0 32)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x12a936 4 0 32).toInstrSpec (shr_r64_imm8_effect_step 0x12a936 0x48 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a93a [0x48, 0x39, 0xF8] (fun s => s.RIP = 0x12a93a) (cmpR64R64Effect 0x12a93a 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x12a93a 0 7).toInstrSpec (cmp_r64_r64_effect_step 0x12a93a 0x48 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a936) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a93a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a93d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x12a93d 4 0x72) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a932 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a932 :=
  Rest.liftedBlock (rest_l12a932 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a932 x hx)

theorem rest_l12a93f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a93f bytes_l12a93f) (entryMap (live .l12a93f))
      2 0x12a93f bytes_l12a93f b_l12a93f := by
  have f0 : InstrSpec 0x12a93f [0x66, 0x39, 0xF8] (fun s => s.RIP = 0x12a93f) (cmpR16R16Effect 0x12a93f 3 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR16R16Effect_footprint 0x12a93f 3 0 7).toInstrSpec (cmp_r16_r16_effect_step 0x12a93f 0xf8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a942) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a942 5 0xa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a93f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a93f :=
  Rest.liftedBlock (rest_l12a93f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a93f x hx)

theorem rest_l12a944 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a944 bytes_l12a944) (entryMap (live .l12a944))
      4 0x12a944 bytes_l12a944 b_l12a944 := by
  have f0 : InstrSpec 0x12a944 [0xC1, 0xEF, 0x10] (fun s => s.RIP = 0x12a944) (shrR32Effect 0x12a944 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a944 3 7 16).toInstrSpec (shr_r32_imm8_effect_step 0x12a944 0xef 0x10 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a947 [0xC1, 0xE8, 0x10] (fun s => s.RIP = 0x12a947) (shrR32Effect 0x12a947 3 0 16)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a947 3 0 16).toInstrSpec (shr_r32_imm8_effect_step 0x12a947 0xe8 0x10 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a94a [0x39, 0xF8] (fun s => s.RIP = 0x12a94a) (cmpR32R32Effect 0x12a94a 2 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x12a94a 2 0 7).toInstrSpec (cmp_r32_r32_effect_step 0x12a94a 0xf8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a947) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a94a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a94c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x12a94c 4 0x63) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a944 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a944 :=
  Rest.liftedBlock (rest_l12a944 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a944 x hx)

theorem rest_l12a94e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a94e bytes_l12a94e) (entryMap (live .l12a94e))
      2 0x12a94e bytes_l12a94e b_l12a94e := by
  have f0 : InstrSpec 0x12a94e [0x40, 0x38, 0xF8] (fun s => s.RIP = 0x12a94e) (cmpR8R8Effect 0x12a94e 3 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x12a94e 3 0 7).toInstrSpec (cmp_r8_r8_rex_effect_step 0x12a94e 0x40 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a951) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a951 5 0x11) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a94e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a94e :=
  Rest.liftedBlock (rest_l12a94e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a94e x hx)

theorem rest_l12a953 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a953 bytes_l12a953) (entryMap (live .l12a953))
      6 0x12a953 bytes_l12a953 b_l12a953 := by
  have f0 : InstrSpec 0x12a953 [0x0F, 0xB7, 0xFF] (fun s => s.RIP = 0x12a953) (movzxR32R16Effect 0x12a953 3 7 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (movzxR32R16Effect_footprint 0x12a953 3 7 7).toInstrSpec (movzx_r32_r16_effect_step 0x12a953 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x12a956 [0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x12a956) (shrR32Effect 0x12a956 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a956 3 7 8).toInstrSpec (shr_r32_imm8_effect_step 0x12a956 0xef 0x8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a959 [0x0F, 0xB7, 0xC0] (fun s => s.RIP = 0x12a959) (movzxR32R16Effect 0x12a959 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R16Effect_footprint 0x12a959 3 0 0).toInstrSpec (movzx_r32_r16_effect_step 0x12a959 0xc0 (by decide)) pre_rip
  have f3 : InstrSpec 0x12a95c [0xC1, 0xE8, 0x08] (fun s => s.RIP = 0x12a95c) (shrR32Effect 0x12a95c 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a95c 3 0 8).toInstrSpec (shr_r32_imm8_effect_step 0x12a95c 0xe8 0x8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a95f [0x66, 0x39, 0xF8] (fun s => s.RIP = 0x12a95f) (cmpR16R16Effect 0x12a95f 3 0 7)
      [.gpr 0, .gpr 7] [] [.flags, .rip] :=
    (cmpR16R16Effect_footprint 0x12a95f 3 0 7).toInstrSpec (cmp_r16_r16_effect_step 0x12a95f 0xf8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a956) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a959) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a95c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a95f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a962) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x12a962 4 0x4d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a953 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a953 :=
  Rest.liftedBlock (rest_l12a953 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a953 x hx)

theorem rest_l12a964 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a964 bytes_l12a964) (entryMap (live .l12a964))
      3 0x12a964 bytes_l12a964 b_l12a964 := by
  have f0 : InstrSpec 0x12a964 [0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x12a964) (movzxR32R8Effect 0x12a964 3 0 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x12a964 3 0 0).toInstrSpec (movzx_r32_r8_effect_step 0x12a964 0xc0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a967 [0x40, 0x0F, 0xB6, 0xCF] (fun s => s.RIP = 0x12a967) (movzxR32R8Effect 0x12a967 4 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x12a967 4 1 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12a967 0x40 (by decide) 0xcf (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a967) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a96b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel8_effect_step 0x12a96b 0x4f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12a964 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a964 :=
  Rest.liftedBlock (rest_l12a964 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a964 x hx)

theorem rest_l12a96d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a96d bytes_l12a96d) (entryMap (live .l12a96d))
      2 0x12a96d bytes_l12a96d b_l12a96d := by
  have f0 : InstrSpec 0x12a96d [0x66, 0x39, 0xFE] (fun s => s.RIP = 0x12a96d) (cmpR16R16Effect 0x12a96d 3 6 7)
      [.gpr 6, .gpr 7] [] [.flags, .rip] :=
    (cmpR16R16Effect_footprint 0x12a96d 3 6 7).toInstrSpec (cmp_r16_r16_effect_step 0x12a96d 0xfe (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a970) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a970 5 0xa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a96d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a96d :=
  Rest.liftedBlock (rest_l12a96d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a96d x hx)

theorem rest_l12a972 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a972 bytes_l12a972) (entryMap (live .l12a972))
      4 0x12a972 bytes_l12a972 b_l12a972 := by
  have f0 : InstrSpec 0x12a972 [0xC1, 0xEF, 0x10] (fun s => s.RIP = 0x12a972) (shrR32Effect 0x12a972 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a972 3 7 16).toInstrSpec (shr_r32_imm8_effect_step 0x12a972 0xef 0x10 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x12a975 [0xC1, 0xEE, 0x10] (fun s => s.RIP = 0x12a975) (shrR32Effect 0x12a975 3 6 16)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a975 3 6 16).toInstrSpec (shr_r32_imm8_effect_step 0x12a975 0xee 0x10 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a978 [0x39, 0xFE] (fun s => s.RIP = 0x12a978) (cmpR32R32Effect 0x12a978 2 6 7)
      [.gpr 6, .gpr 7] [] [.flags, .rip] :=
    (cmpR32R32Effect_footprint 0x12a978 2 6 7).toInstrSpec (cmp_r32_r32_effect_step 0x12a978 0xfe (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a975) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a978) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a97a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x12a97a 4 0x35) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a972 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a972 :=
  Rest.liftedBlock (rest_l12a972 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a972 x hx)

theorem rest_l12a97c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a97c bytes_l12a97c) (entryMap (live .l12a97c))
      2 0x12a97c bytes_l12a97c b_l12a97c := by
  have f0 : InstrSpec 0x12a97c [0x40, 0x38, 0xFE] (fun s => s.RIP = 0x12a97c) (cmpR8R8Effect 0x12a97c 3 6 7)
      [.gpr 6, .gpr 7] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x12a97c 3 6 7).toInstrSpec (cmp_r8_r8_rex_effect_step 0x12a97c 0x40 0xfe (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a97f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a97f 5 0x11) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a97c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a97c :=
  Rest.liftedBlock (rest_l12a97c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a97c x hx)

theorem rest_l12a981 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a981 bytes_l12a981) (entryMap (live .l12a981))
      6 0x12a981 bytes_l12a981 b_l12a981 := by
  have f0 : InstrSpec 0x12a981 [0x0F, 0xB7, 0xFF] (fun s => s.RIP = 0x12a981) (movzxR32R16Effect 0x12a981 3 7 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (movzxR32R16Effect_footprint 0x12a981 3 7 7).toInstrSpec (movzx_r32_r16_effect_step 0x12a981 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x12a984 [0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x12a984) (shrR32Effect 0x12a984 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a984 3 7 8).toInstrSpec (shr_r32_imm8_effect_step 0x12a984 0xef 0x8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a987 [0x0F, 0xB7, 0xF6] (fun s => s.RIP = 0x12a987) (movzxR32R16Effect 0x12a987 3 6 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (movzxR32R16Effect_footprint 0x12a987 3 6 6).toInstrSpec (movzx_r32_r16_effect_step 0x12a987 0xf6 (by decide)) pre_rip
  have f3 : InstrSpec 0x12a98a [0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x12a98a) (shrR32Effect 0x12a98a 3 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a98a 3 6 8).toInstrSpec (shr_r32_imm8_effect_step 0x12a98a 0xee 0x8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a98d [0x66, 0x39, 0xFE] (fun s => s.RIP = 0x12a98d) (cmpR16R16Effect 0x12a98d 3 6 7)
      [.gpr 6, .gpr 7] [] [.flags, .rip] :=
    (cmpR16R16Effect_footprint 0x12a98d 3 6 7).toInstrSpec (cmp_r16_r16_effect_step 0x12a98d 0xfe (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a984) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a987) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a98a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a98d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a990) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x12a990 4 0x1f) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a981 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a981 :=
  Rest.liftedBlock (rest_l12a981 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a981 x hx)

theorem rest_l12a992 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a992 bytes_l12a992) (entryMap (live .l12a992))
      2 0x12a992 bytes_l12a992 b_l12a992 := by
  have f0 : InstrSpec 0x12a992 [0x40, 0x0F, 0xB6, 0xC6] (fun s => s.RIP = 0x12a992) (movzxR32R8Effect 0x12a992 4 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x12a992 4 0 6).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12a992 0x40 (by decide) 0xc6 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a996) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel8_effect_step 0x12a996 0x20 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12a992 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a992 :=
  Rest.liftedBlock (rest_l12a992 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a992 x hx)

theorem rest_l12a998 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a998 bytes_l12a998) (entryMap (live .l12a998))
      2 0x12a998 bytes_l12a998 b_l12a998 := by
  have f0 : InstrSpec 0x12a998 [0x41, 0x38, 0xF8] (fun s => s.RIP = 0x12a998) (cmpR8R8Effect 0x12a998 3 8 7)
      [.gpr 8, .gpr 7] [] [.flags, .rip] :=
    (cmpR8R8Effect_footprint 0x12a998 3 8 7).toInstrSpec (cmp_r8_r8_rex_effect_step 0x12a998 0x41 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a99b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x12a99b 5 0x17) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a998 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a998 :=
  Rest.liftedBlock (rest_l12a998 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a998 x hx)

theorem rest_l12a99d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a99d bytes_l12a99d) (entryMap (live .l12a99d))
      6 0x12a99d bytes_l12a99d b_l12a99d := by
  have f0 : InstrSpec 0x12a99d [0x0F, 0xB7, 0xFF] (fun s => s.RIP = 0x12a99d) (movzxR32R16Effect 0x12a99d 3 7 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (movzxR32R16Effect_footprint 0x12a99d 3 7 7).toInstrSpec (movzx_r32_r16_effect_step 0x12a99d 0xff (by decide)) pre_rip
  have f1 : InstrSpec 0x12a9a0 [0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x12a9a0) (shrR32Effect 0x12a9a0 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a9a0 3 7 8).toInstrSpec (shr_r32_imm8_effect_step 0x12a9a0 0xef 0x8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12a9a3 [0x45, 0x0F, 0xB7, 0xC0] (fun s => s.RIP = 0x12a9a3) (movzxR32R16Effect 0x12a9a3 4 8 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (movzxR32R16Effect_footprint 0x12a9a3 4 8 8).toInstrSpec (movzx_r32_r16_rex_effect_step 0x12a9a3 0x45 (by decide) 0xc0 (by decide)) pre_rip
  have f3 : InstrSpec 0x12a9a7 [0x41, 0xC1, 0xE8, 0x08] (fun s => s.RIP = 0x12a9a7) (shrR32Effect 0x12a9a7 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x12a9a7 4 8 8).toInstrSpec (shr_r32_imm8_rex_effect_step 0x12a9a7 0x41 0xe8 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12a9ab [0x66, 0x41, 0x39, 0xF8] (fun s => s.RIP = 0x12a9ab) (cmpR16R16Effect 0x12a9ab 4 8 7)
      [.gpr 8, .gpr 7] [] [.flags, .rip] :=
    (cmpR16R16Effect_footprint 0x12a9ab 4 8 7).toInstrSpec (cmp_r16_r16_rex_effect_step 0x12a9ab 0x41 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a9a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a9a3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a9a7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a9ab) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a9af) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel8_effect_step 0x12a9af 5 0x3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12a99d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a99d :=
  Rest.liftedBlock (rest_l12a99d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a99d x hx)

theorem rest_l12a9b1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a9b1 bytes_l12a9b1) (entryMap (live .l12a9b1))
      2 0x12a9b1 bytes_l12a9b1 b_l12a9b1 := by
  have f0 : InstrSpec 0x12a9b1 [0x31, 0xC0] (fun s => s.RIP = 0x12a9b1) (xorR32R32Effect 0x12a9b1 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x12a9b1 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x12a9b1 0xc0 (by decide)) pre_rip
  have f1 : InstrSpec 0x12a9b3 [0xC3] (RetPre 0x12a9b3) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a9b3).toInstrSpec (ret_effect_step 0x12a9b3) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a9b3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l12a9b1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a9b1 :=
  Rest.liftedBlock (rest_l12a9b1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a9b1 x hx)

theorem rest_l12a9b4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a9b4 bytes_l12a9b4) (entryMap (live .l12a9b4))
      1 0x12a9b4 bytes_l12a9b4 b_l12a9b4 := by
  have f0 : InstrSpec 0x12a9b4 [0x41, 0x0F, 0xB6, 0xC0] (fun s => s.RIP = 0x12a9b4) (movzxR32R8Effect 0x12a9b4 4 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movzxR32R8Effect_footprint 0x12a9b4 4 0 8).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12a9b4 0x41 (by decide) 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a9b8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l12a9b4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a9b4 :=
  Rest.liftedBlock (rest_l12a9b4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a9b4 x hx)

theorem rest_l12a9b8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a9b8 bytes_l12a9b8) (entryMap (live .l12a9b8))
      1 0x12a9b8 bytes_l12a9b8 b_l12a9b8 := by
  have f0 : InstrSpec 0x12a9b8 [0x40, 0x0F, 0xB6, 0xCF] (fun s => s.RIP = 0x12a9b8) (movzxR32R8Effect 0x12a9b8 4 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movzxR32R8Effect_footprint 0x12a9b8 4 1 7).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12a9b8 0x40 (by decide) 0xcf (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a9bc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l12a9b8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a9b8 :=
  Rest.liftedBlock (rest_l12a9b8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a9b8 x hx)

theorem rest_l12a9bc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a9bc bytes_l12a9bc) (entryMap (live .l12a9bc))
      1 0x12a9bc bytes_l12a9bc b_l12a9bc := by
  have f0 : InstrSpec 0x12a9bc [0x29, 0xC8] (fun s => s.RIP = 0x12a9bc) (subR32R32Effect 0x12a9bc 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (subR32R32Effect_footprint 0x12a9bc 2 0 1).toInstrSpec (sub_r32_r32_effect_step 0x12a9bc 0xc8 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a9be) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l12a9bc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a9bc :=
  Rest.liftedBlock (rest_l12a9bc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a9bc x hx)

theorem rest_l12a9be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12a9be bytes_l12a9be) (entryMap (live .l12a9be))
      1 0x12a9be bytes_l12a9be b_l12a9be := by
  have f0 : InstrSpec 0x12a9be [0xC3] (RetPre 0x12a9be) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12a9be).toInstrSpec (ret_effect_step 0x12a9be) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f0 (by decide) rfl rfl rfl (by decide)

theorem block_l12a9be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12a9be :=
  Rest.liftedBlock (rest_l12a9be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12a9be x hx)

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

theorem_by block_l12a850_eval :
    program.runBlock (dialect code) ⟨.l12a850, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a860_eval :
    program.runBlock (dialect code) ⟨.l12a860, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a870_eval :
    program.runBlock (dialect code) ⟨.l12a870, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a881_eval :
    program.runBlock (dialect code) ⟨.l12a881, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a88a_eval :
    program.runBlock (dialect code) ⟨.l12a88a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a890_eval :
    program.runBlock (dialect code) ⟨.l12a890, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a8a0_eval :
    program.runBlock (dialect code) ⟨.l12a8a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a8b0_eval :
    program.runBlock (dialect code) ⟨.l12a8b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a8c0_eval :
    program.runBlock (dialect code) ⟨.l12a8c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a8c9_eval :
    program.runBlock (dialect code) ⟨.l12a8c9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a8cf_eval :
    program.runBlock (dialect code) ⟨.l12a8cf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a8d8_eval :
    program.runBlock (dialect code) ⟨.l12a8d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a8f0_eval :
    program.runBlock (dialect code) ⟨.l12a8f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a904_eval :
    program.runBlock (dialect code) ⟨.l12a904, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a90d_eval :
    program.runBlock (dialect code) ⟨.l12a90d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a910_eval :
    program.runBlock (dialect code) ⟨.l12a910, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a91b_eval :
    program.runBlock (dialect code) ⟨.l12a91b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a929_eval :
    program.runBlock (dialect code) ⟨.l12a929, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a92e_eval :
    program.runBlock (dialect code) ⟨.l12a92e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a932_eval :
    program.runBlock (dialect code) ⟨.l12a932, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a93f_eval :
    program.runBlock (dialect code) ⟨.l12a93f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a944_eval :
    program.runBlock (dialect code) ⟨.l12a944, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a94e_eval :
    program.runBlock (dialect code) ⟨.l12a94e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a953_eval :
    program.runBlock (dialect code) ⟨.l12a953, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a964_eval :
    program.runBlock (dialect code) ⟨.l12a964, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a96d_eval :
    program.runBlock (dialect code) ⟨.l12a96d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a972_eval :
    program.runBlock (dialect code) ⟨.l12a972, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a97c_eval :
    program.runBlock (dialect code) ⟨.l12a97c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a981_eval :
    program.runBlock (dialect code) ⟨.l12a981, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a992_eval :
    program.runBlock (dialect code) ⟨.l12a992, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a998_eval :
    program.runBlock (dialect code) ⟨.l12a998, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a99d_eval :
    program.runBlock (dialect code) ⟨.l12a99d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a9b1_eval :
    program.runBlock (dialect code) ⟨.l12a9b1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a9b4_eval :
    program.runBlock (dialect code) ⟨.l12a9b4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a9b8_eval :
    program.runBlock (dialect code) ⟨.l12a9b8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a9bc_eval :
    program.runBlock (dialect code) ⟨.l12a9bc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12a9be_eval :
    program.runBlock (dialect code) ⟨.l12a9be, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
