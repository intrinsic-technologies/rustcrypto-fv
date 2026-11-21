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

theorem rest_l125760 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125760 bytes_l125760) (entryMap (live .l125760))
      2 0x125760 bytes_l125760 b_l125760 := by
  have f0 : InstrSpec 0x125760 [0x48, 0x85, 0xF6] (fun s => s.RIP = 0x125760) (testR64R64Effect 0x125760 6 6)
      [.gpr 6, .gpr 6] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x125760 6 6).toInstrSpec (test_r64_r64_effect_step 0x125760 0x48 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125763) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x125763 4 0xa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125760 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125760 :=
  Rest.liftedBlock (rest_l125760 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125760 x hx)

theorem rest_l125765 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125765 bytes_l125765) (entryMap (live .l125765))
      4 0x125765 bytes_l125765 b_l125765 := by
  have f0 : InstrSpec 0x125765 [0x0F, 0xB6, 0x44, 0x37, 0xFF] (LoadPre 0x125765 (fun s => AddrMode.addr (.sib 7 (some 6) 0 (.d8 0xff)) s (0x125765 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125765 5 0 (.sib 7 (some 6) 0 (.d8 0xff)))
      [.gpr 7, .gpr 6] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x125765 5 0 (.sib 7 (some 6) 0 (.d8 0xff))).toInstrSpec (movzx_r32_m8_effect_step 0x125765 0 (.sib 7 (some 6) 0 (.d8 0xff)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12576a [0x24, 0x01] (fun s => s.RIP = 0x12576a) (andAlImm8Effect 0x12576a 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x12576a 0x1).toInstrSpec (and_al_imm8_effect_step 0x12576a 0x1) pre_rip
  have f2 : InstrSpec 0x12576c [0x0C, 0x02] (fun s => s.RIP = 0x12576c) (orAlImm8Effect 0x12576c 0x2)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (orAlImm8Effect_footprint 0x12576c 0x2).toInstrSpec (or_al_imm8_effect_step 0x12576c 0x2) pre_rip
  have f3 : InstrSpec 0x12576e [0xC3] (RetPre 0x12576e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x12576e).toInstrSpec (ret_effect_step 0x12576e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12576a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12576c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12576e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l125765 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125765 :=
  Rest.liftedBlock (rest_l125765 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125765 x hx)

theorem rest_l12576f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12576f bytes_l12576f) (entryMap (live .l12576f))
      5 0x12576f bytes_l12576f b_l12576f := by
  have f0 : InstrSpec 0x12576f [0x50] (PushPre 0x12576f 1) (pushR64Effect 0x12576f 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12576f 1 0).toInstrSpec (push_r64_effect_step 0x12576f 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x125770 [0xBE, 0x12, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125770) (movR32Imm32Effect 0x125770 5 6 0x12)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x125770 5 6 0x12).toInstrSpec (mov_r32_imm32_effect_step 0x125770 0xbe (by decide) 0x12) pre_rip
  have f2 : InstrSpec 0x125775 [0x48, 0xC7, 0xC7, 0xB0, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x125775) (movR64Imm32Effect 0x125775 7 0x2036b0)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x125775 7 0x2036b0).toInstrSpec (mov_r64_imm32_effect_step 0x125775 0x48 0xc7 (by decide) (by decide) (by decide) 0x2036b0) pre_rip
  have f3 : InstrSpec 0x12577c [0x48, 0xC7, 0xC2, 0xC8, 0x36, 0x20, 0x00] (fun s => s.RIP = 0x12577c) (movR64Imm32Effect 0x12577c 2 0x2036c8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x12577c 2 0x2036c8).toInstrSpec (mov_r64_imm32_effect_step 0x12577c 0x48 0xc2 (by decide) (by decide) (by decide) 0x2036c8) pre_rip
  have f4 : InstrSpec 0x125783 [0xE8, 0xD8, 0x3D, 0x00, 0x00] (PushPre 0x125783 5) (callEffect (fun _ => 0x129560) 0x125788)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x125783 0x129560 0x125788).toInstrSpec (call_rel32_effect_step 0x125783 0x3dd8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 53), (5, 5)]) (p' := 0x125770) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (4, 53), (5, 5), (6, 55)]) (p' := 0x125775) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (4, 53), (5, 5), (6, 55), (7, 57)]) (p' := 0x12577c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (4, 53), (5, 5), (6, 55), (7, 57)]) (p' := 0x125783) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 59), (4, 61), (5, 5), (6, 55), (7, 57)]) (p' := 0x129560) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l12576f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12576f :=
  Rest.liftedBlock (rest_l12576f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12576f x hx)

theorem rest_l125788 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125788 bytes_l125788) (entryMap (live .l125788))
      9 0x125788 bytes_l125788 b_l125788 := by
  have f0 : InstrSpec 0x125788 [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125788) (fun _ => nopEffect 0x125788 8)
      [] [] [.rip] :=
    (nopEffect_footprint 0x125788 8).toInstrSpec (nop_m_effect_step 0x125788 [] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x125790 [0x55] (PushPre 0x125790 1) (pushR64Effect 0x125790 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125790 1 5).toInstrSpec (push_r64_effect_step 0x125790 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x125791 [0x41, 0x57] (PushPre 0x125791 2) (pushR64Effect 0x125791 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125791 2 15).toInstrSpec (push_r64_rex_effect_step 0x125791 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x125793 [0x41, 0x56] (PushPre 0x125793 2) (pushR64Effect 0x125793 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125793 2 14).toInstrSpec (push_r64_rex_effect_step 0x125793 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x125795 [0x53] (PushPre 0x125795 1) (pushR64Effect 0x125795 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x125795 1 3).toInstrSpec (push_r64_effect_step 0x125795 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x125796 [0x48, 0x81, 0xEC, 0x38, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x125796) (subR64Imm32Effect 0x125796 4 0x138)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x125796 4 0x138).toInstrSpec (sub_r64_imm32_effect_step 0x125796 0x48 0xec 0x138 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x12579d [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x12579d) (movR64R64Effect 0x12579d 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x12579d 3 7).toInstrSpec (mov_r64_r64_effect_step 0x12579d 0x48 0xfb (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1257a0 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x1257a0) (leaR64Effect 0x1257a0 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1257a0 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1257a0 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1257a5 [0xE8, 0xE6, 0x1E, 0x00, 0x00] (PushPre 0x1257a5 5) (callEffect (fun _ => 0x127690) 0x1257aa)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1257a5 0x127690 0x1257aa).toInstrSpec (call_rel32_effect_step 0x1257a5 0x1ee6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125790) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125791) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125793) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125795) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125796) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 2), (3, 3), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12579d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 2), (3, 64), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257a0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(2, 2), (3, 64), (4, 62), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257a5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 64), (4, 68), (5, 5), (6, 6), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127690) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l125788 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125788 :=
  Rest.liftedBlock (rest_l125788 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125788 x hx)

theorem rest_l1257aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1257aa bytes_l1257aa) (entryMap (live .l1257aa))
      3 0x1257aa bytes_l1257aa b_l1257aa := by
  have f0 : InstrSpec 0x1257aa [0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1257aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1257aa + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1257aa 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1257aa 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1257aa 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1257ae [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1257ae) (cmpR32Imm8Effect 0x1257ae 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1257ae 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1257ae 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257ae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257b1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1257b1 5 0x23d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1257aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1257aa :=
  Rest.liftedBlock (rest_l1257aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1257aa x hx)

theorem rest_l1257b7_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x1257b7 bytes_l1257b7) [(0, 79), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      9 0x125832 bytes_l1257b7_1 b_l1257b7_1 := by
  have f20 : InstrSpec 0x125832 [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x125832 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125832 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125832 0 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x125832 0 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x125832 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x12583a [0x48, 0x89, 0x84, 0x24, 0xE4, 0x00, 0x00, 0x00] (StorePre 0x12583a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe4)) s (0x12583a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12583a 0 (.sib 4 none 0 (.d32 0xe4)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12583a 0 (.sib 4 none 0 (.d32 0xe4))).toInstrSpec (mov_m64_r64_effect_step 0x12583a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xe4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x125842 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x125842 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125842 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125842 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x125842 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x125842 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x12584a [0x48, 0x8B, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x12584a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x12584a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12584a 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12584a 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x12584a 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x125852 [0x48, 0x89, 0x8C, 0x24, 0xDC, 0x00, 0x00, 0x00] (StorePre 0x125852 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xdc)) s (0x125852 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125852 1 (.sib 4 none 0 (.d32 0xdc)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125852 1 (.sib 4 none 0 (.d32 0xdc))).toInstrSpec (mov_m64_r64_effect_step 0x125852 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xdc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x12585a [0x48, 0x89, 0x84, 0x24, 0xD4, 0x00, 0x00, 0x00] (StorePre 0x12585a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd4)) s (0x12585a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12585a 0 (.sib 4 none 0 (.d32 0xd4)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12585a 0 (.sib 4 none 0 (.d32 0xd4))).toInstrSpec (mov_m64_r64_effect_step 0x12585a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x125862 [0x48, 0x8D, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125862) (leaR64Effect 0x125862 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x125862 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x125862 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x12586a [0x48, 0x8D, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12586a) (leaR64Effect 0x12586a 6 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x12586a 6 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (lea_r64_effect_step 0x12586a 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x125872 [0xE8, 0xD9, 0xFB, 0xFF, 0xFF] (PushPre 0x125872 5) (callEffect (fun _ => 0x125450) 0x125877)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x125872 0x125450 0x125877).toInstrSpec (call_rel32_effect_step 0x125872 0xfffffbd9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f20 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12583a) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125842) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12584a) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (1, 87), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125852) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 85), (1, 87), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12585a) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 85), (1, 87), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125862) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f26 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 85), (1, 87), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12586a) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f27 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 85), (1, 87), (2, 58), (3, 3), (4, 4), (5, 5), (6, 93), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125872) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f28 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 85), (1, 87), (2, 58), (3, 3), (4, 95), (5, 5), (6, 93), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125450) f28 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 97) (by decide) (by decide) rfl rfl

theorem rest_l1257b7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1257b7 bytes_l1257b7) (entryMap (live .l1257b7))
      29 0x1257b7 bytes_l1257b7 b_l1257b7 := by
  have f0 : InstrSpec 0x1257b7 [0x0F, 0xB6, 0x44, 0x24, 0x10] (LoadPre 0x1257b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1257b7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1257b7 5 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1257b7 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1257b7 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1257bc [0x0F, 0xB7, 0x4C, 0x24, 0x11] (LoadPre 0x1257bc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1257bc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1257bc 5 1 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x1257bc 5 1 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m16_effect_step 0x1257bc 1 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1257c1 [0x66, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x1257c1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1257c1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1257c1 5 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1257c1 5 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m16_r16_effect_step 0x1257c1 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1257c6 [0x0F, 0xB6, 0x54, 0x24, 0x13] (LoadPre 0x1257c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x1257c6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1257c6 5 2 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1257c6 5 2 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m8_effect_step 0x1257c6 2 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1257cb [0x88, 0x54, 0x24, 0x62] (StorePre 0x1257cb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x1257cb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1257cb 4 2 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1257cb 4 2 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (mov_m8_r8_effect_step 0x1257cb 2 (by decide) (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1257cf [0x48, 0x8B, 0x74, 0x24, 0x14] (LoadPre 0x1257cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1257cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1257cf 6 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1257cf 6 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x1257cf 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1257d4 [0x48, 0x8B, 0x7C, 0x24, 0x1C] (LoadPre 0x1257d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1257d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1257d4 7 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1257d4 7 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x1257d4 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1257d9 [0x48, 0x89, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x1257d9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1257d9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1257d9 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1257d9 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x1257d9 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1257e1 [0x48, 0x8B, 0x7C, 0x24, 0x24] (LoadPre 0x1257e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1257e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1257e1 7 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1257e1 7 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x1257e1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1257e6 [0x48, 0x89, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1257e6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1257e6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1257e6 7 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1257e6 7 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1257e6 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1257ee [0x48, 0x8B, 0x7C, 0x24, 0x2C] (LoadPre 0x1257ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1257ee + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1257ee 7 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1257ee 7 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x1257ee 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1257f3 [0x48, 0x89, 0xBC, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1257f3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1257f3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1257f3 7 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1257f3 7 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1257f3 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1257fb [0x8B, 0x7C, 0x24, 0x34] (LoadPre 0x1257fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1257fb + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1257fb 7 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x1257fb 7 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x1257fb 7 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1257ff [0x89, 0xBC, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1257ff 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1257ff + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1257ff 7 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1257ff 7 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m32_r32_low_effect_step 0x1257ff 7 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125806 [0x88, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x125806 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x125806 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x125806 7 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125806 7 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m8_r8_effect_step 0x125806 0 (by decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x12580d [0x66, 0x89, 0x8C, 0x24, 0xC9, 0x00, 0x00, 0x00] (StorePre 0x12580d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc9)) s (0x12580d + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x12580d 8 1 (.sib 4 none 0 (.d32 0xc9)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x12580d 8 1 (.sib 4 none 0 (.d32 0xc9))).toInstrSpec (mov_m16_r16_effect_step 0x12580d 1 (.sib 4 none 0 (.d32 0xc9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x125815 [0x88, 0x94, 0x24, 0xCB, 0x00, 0x00, 0x00] (StorePre 0x125815 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb)) s (0x125815 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x125815 7 2 (.sib 4 none 0 (.d32 0xcb)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125815 7 2 (.sib 4 none 0 (.d32 0xcb))).toInstrSpec (mov_m8_r8_effect_step 0x125815 2 (by decide) (.sib 4 none 0 (.d32 0xcb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x12581c [0x48, 0x89, 0xB4, 0x24, 0xCC, 0x00, 0x00, 0x00] (StorePre 0x12581c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x12581c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12581c 6 (.sib 4 none 0 (.d32 0xcc)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12581c 6 (.sib 4 none 0 (.d32 0xcc))).toInstrSpec (mov_m64_r64_effect_step 0x12581c 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xcc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x125824 [0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x125824 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125824 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x125824 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x125824 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r32_m32_low_effect_step 0x125824 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x12582b [0x89, 0x84, 0x24, 0xEC, 0x00, 0x00, 0x00] (StorePre 0x12582b 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xec)) s (0x12582b + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x12582b 0 (.sib 4 none 0 (.d32 0xec)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12582b 0 (.sib 4 none 0 (.d32 0xec))).toInstrSpec (mov_m32_r32_low_effect_step 0x12582b 0 (.sib 4 none 0 (.d32 0xec)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257bc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257c1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257c6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257cb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257cf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257d4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257d9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257e1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257e6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257ee) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257f3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257fb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1257ff) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125806) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12580d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125815) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12581c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125824) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12582b) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 55), (2, 58), (3, 3), (4, 4), (5, 5), (6, 61), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125832) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1257b7_1 code

theorem block_l1257b7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1257b7 :=
  Rest.liftedBlock (rest_l1257b7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1257b7 x hx)

theorem rest_l125877 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125877 bytes_l125877) (entryMap (live .l125877))
      7 0x125877 bytes_l125877 b_l125877 := by
  have f0 : InstrSpec 0x125877 [0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x125877 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125877 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x125877 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x125877 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r32_m32_low_effect_step 0x125877 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12587e [0x48, 0x8B, 0x8C, 0x24, 0x84, 0x00, 0x00, 0x00] (LoadPre 0x12587e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x12587e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12587e 1 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12587e 1 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_r64_m64_effect_step 0x12587e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125886 [0x48, 0x89, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00] (StorePre 0x125886 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x125886 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125886 1 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125886 1 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_m64_r64_effect_step 0x125886 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x12588e [0x48, 0x8B, 0x8C, 0x24, 0x8C, 0x00, 0x00, 0x00] (LoadPre 0x12588e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x12588e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12588e 1 (.sib 4 none 0 (.d32 0x8c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12588e 1 (.sib 4 none 0 (.d32 0x8c))).toInstrSpec (mov_r64_m64_effect_step 0x12588e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x8c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x125896 [0x48, 0x89, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00] (StorePre 0x125896 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x125896 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125896 1 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125896 1 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_m64_r64_effect_step 0x125896 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x12589e [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x12589e) (cmpR32Imm8Effect 0x12589e 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x12589e 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x12589e 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12587e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125886) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12588e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125896) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12589e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258a1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel32_effect_step 0x1258a1 5 0x205) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125877 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125877 :=
  Rest.liftedBlock (rest_l125877 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125877 x hx)

theorem rest_l1258a7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1258a7 bytes_l1258a7) (entryMap (live .l1258a7))
      7 0x1258a7 bytes_l1258a7 b_l1258a7 := by
  have f0 : InstrSpec 0x1258a7 [0x48, 0x8B, 0xB4, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x1258a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x1258a7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1258a7 6 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1258a7 6 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x1258a7 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1258af [0x48, 0x8B, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x1258af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x1258af + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1258af 0 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1258af 0 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x1258af 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1258b7 [0x48, 0x89, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x1258b7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1258b7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1258b7 6 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1258b7 6 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x1258b7 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1258bf [0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x1258bf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1258bf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1258bf 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1258bf 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x1258bf 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1258c7 [0x48, 0x8D, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1258c7) (leaR64Effect 0x1258c7 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1258c7 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (lea_r64_effect_step 0x1258c7 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1258cf [0xBA, 0x0A, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1258cf) (movR32Imm32Effect 0x1258cf 5 2 0xa)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1258cf 5 2 0xa).toInstrSpec (mov_r32_imm32_effect_step 0x1258cf 0xba (by decide) 0xa) pre_rip
  have f6 : InstrSpec 0x1258d4 [0xE8, 0xF7, 0x1D, 0x00, 0x00] (PushPre 0x1258d4 5) (callEffect (fun _ => 0x1276d0) 0x1258d9)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1258d4 0x1276d0 0x1258d9).toInstrSpec (call_rel32_effect_step 0x1258d4 0x1df7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258af) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258b7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258bf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258c7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258cf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 4), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258d4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (2, 61), (3, 3), (4, 63), (5, 5), (6, 53), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d0) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l1258a7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1258a7 :=
  Rest.liftedBlock (rest_l1258a7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1258a7 x hx)

theorem rest_l1258d9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1258d9 bytes_l1258d9) (entryMap (live .l1258d9))
      3 0x1258d9 bytes_l1258d9 b_l1258d9 := by
  have f0 : InstrSpec 0x1258d9 [0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x1258d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1258d9 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1258d9 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1258d9 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r32_m32_low_effect_step 0x1258d9 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1258e0 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1258e0) (cmpR32Imm8Effect 0x1258e0 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1258e0 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1258e0 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258e0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258e3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1258e3 5 0x21e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1258d9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1258d9 :=
  Rest.liftedBlock (rest_l1258d9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1258d9 x hx)

theorem rest_l1258e9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1258e9 bytes_l1258e9) (entryMap (live .l1258e9))
      4 0x1258e9 bytes_l1258e9 b_l1258e9 := by
  have f0 : InstrSpec 0x1258e9 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x1258e9) (leaR64Effect 0x1258e9 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1258e9 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1258e9 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1258ee [0x48, 0x8D, 0xB4, 0x24, 0xC8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1258ee) (leaR64Effect 0x1258ee 6 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1258ee 6 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (lea_r64_effect_step 0x1258ee 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1258f6 [0x48, 0x8D, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1258f6) (leaR64Effect 0x1258f6 2 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1258f6 2 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (lea_r64_effect_step 0x1258f6 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1258fe [0xE8, 0x2D, 0x11, 0x00, 0x00] (PushPre 0x1258fe 5) (callEffect (fun _ => 0x126a30) 0x125903)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1258fe 0x126a30 0x125903).toInstrSpec (call_rel32_effect_step 0x1258fe 0x112d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258ee) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258f6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1258fe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x126a30) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1258e9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1258e9 :=
  Rest.liftedBlock (rest_l1258e9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1258e9 x hx)

theorem rest_l125903 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125903 bytes_l125903) (entryMap (live .l125903))
      3 0x125903 bytes_l125903 b_l125903 := by
  have f0 : InstrSpec 0x125903 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x125903 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125903 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125903 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x125903 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x125903 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125907 [0x83, 0x7C, 0x24, 0x08, 0x01] (LoadPre 0x125907 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125907 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x125907 5 32 (.sib 4 none 0 (.d8 0x8)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (cmpMImm8Effect32_footprint 0x125907 5 (.sib 4 none 0 (.d8 0x8)) 0x1).toInstrSpec (cmp_m32_imm8_effect_step 0x125907 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125907) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (11, 11), (12, 12), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12590c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x12590c 4 0x24e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125903 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125903 :=
  Rest.liftedBlock (rest_l125903 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125903 x hx)

theorem rest_l125912_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x125912 bytes_l125912) [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 84), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]
      19 0x125973 bytes_l125912_1 b_l125912_1 := by
  have f20 : InstrSpec 0x125973 [0x4C, 0x8B, 0x54, 0x24, 0x50] (LoadPre 0x125973 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x125973 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125973 10 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x125973 10 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x125973 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x125978 [0x4C, 0x89, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00] (StorePre 0x125978 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x125978 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125978 10 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125978 10 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_m64_r64_effect_step 0x125978 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x125980 [0x4C, 0x89, 0x8C, 0x24, 0x20, 0x01, 0x00, 0x00] (StorePre 0x125980 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x125980 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125980 9 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125980 9 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_m64_r64_effect_step 0x125980 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x125988 [0x44, 0x0F, 0xB7, 0x0C, 0x24] (LoadPre 0x125988 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x125988 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x125988 5 9 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x125988 5 9 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x125988 0x44 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x12598d [0x66, 0x44, 0x89, 0x4C, 0x24, 0x04] (StorePre 0x12598d 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x12598d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12598d 6 9 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x12598d 6 9 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m16_r16_rex_effect_step 0x12598d 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x125993 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x02] (LoadPre 0x125993 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x125993 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125993 6 9 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x125993 6 9 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125993 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x125999 [0x44, 0x88, 0x4C, 0x24, 0x06] (StorePre 0x125999 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x125999 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x125999 5 9 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125999 5 9 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125999 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x12599e [0x4C, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x12599e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12599e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12599e 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x12599e 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x12599e 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x1259a3 [0x4C, 0x8B, 0x54, 0x24, 0x68] (LoadPre 0x1259a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1259a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1259a3 10 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1259a3 10 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1259a3 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x1259a8 [0x4C, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (StorePre 0x1259a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1259a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1259a8 9 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1259a8 9 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_m64_r64_effect_step 0x1259a8 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x1259b0 [0x4C, 0x89, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00] (StorePre 0x1259b0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1259b0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1259b0 10 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1259b0 10 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_m64_r64_effect_step 0x1259b0 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x1259b8 [0x4C, 0x8B, 0x4C, 0x24, 0x70] (LoadPre 0x1259b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1259b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1259b8 9 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x1259b8 9 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x1259b8 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x1259bd [0x4C, 0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00] (StorePre 0x1259bd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1259bd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1259bd 9 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1259bd 9 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_m64_r64_effect_step 0x1259bd 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x1259c5 [0x44, 0x8B, 0x4C, 0x24, 0x78] (LoadPre 0x1259c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1259c5 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1259c5 9 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x1259c5 9 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r32_m32_effect_step 0x1259c5 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x1259ca [0x44, 0x89, 0x8C, 0x24, 0x18, 0x01, 0x00, 0x00] (StorePre 0x1259ca 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1259ca + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1259ca 9 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1259ca 9 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_m32_r32_effect_step 0x1259ca 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x1259d2 [0x44, 0x8B, 0x8C, 0x24, 0xE4, 0x00, 0x00, 0x00] (LoadPre 0x1259d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe4)) s (0x1259d2 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x1259d2 9 (.sib 4 none 0 (.d32 0xe4)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x1259d2 9 (.sib 4 none 0 (.d32 0xe4))).toInstrSpec (mov_r32_m32_effect_step 0x1259d2 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xe4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f36 : InstrSpec 0x1259da [0xBD, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1259da) (movR32Imm32Effect 0x1259da 5 5 0x1)
      [] [] [.reg 5, .rip] :=
    (movR32Imm32Effect_footprint 0x1259da 5 5 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1259da 0xbd (by decide) 0x1) pre_rip
  have f37 : InstrSpec 0x1259df [0xF6, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x01] (LoadPre 0x1259df (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1259df + BitVec.ofNat 64 8)) 1) (testM8Imm8Effect 0x1259df 8 (.sib 4 none 0 (.d32 0xe8)) 0x1)
      [.gpr 4] [] [.flags, .rip] :=
    (testM8Imm8Effect_footprint 0x1259df 8 (.sib 4 none 0 (.d32 0xe8)) 0x1).toInstrSpec (test_m8_imm8_effect_step 0x1259df (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide) 0x1) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f20 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 84), (10, 86), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125978) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 84), (10, 86), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125980) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 84), (10, 86), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125988) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 90), (10, 86), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12598d) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 90), (10, 86), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125993) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f25 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 93), (10, 86), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125999) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 93), (10, 86), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12599e) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f27 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 96), (10, 86), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259a3) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f28 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 96), (10, 98), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259a8) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 96), (10, 98), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259b0) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 96), (10, 98), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259b8) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f31 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 102), (10, 98), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259bd) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 102), (10, 98), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259c5) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f33 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 105), (10, 98), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259ca) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 105), (10, 98), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259d2) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f35 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 108), (10, 98), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259da) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f36 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (5, 110), (6, 79), (7, 53), (8, 65), (9, 108), (10, 98), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259df) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f37 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (5, 110), (6, 79), (7, 53), (8, 65), (9, 108), (10, 98), (11, 11), (12, 12), (13, 13), (19, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259e7) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 114) (jcc_rel32_effect_step 0x1259e7 4 0x2c8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l125912 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125912 bytes_l125912) (entryMap (live .l125912))
      39 0x125912 bytes_l125912 b_l125912 := by
  have f0 : InstrSpec 0x125912 [0x8B, 0x7C, 0x24, 0x14] (LoadPre 0x125912 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125912 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125912 7 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x125912 7 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x125912 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125916 [0x0F, 0xB6, 0x4C, 0x24, 0x18] (LoadPre 0x125916 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125916 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125916 5 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x125916 5 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x125916 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12591b [0x0F, 0xB7, 0x54, 0x24, 0x19] (LoadPre 0x12591b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x12591b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x12591b 5 2 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x12591b 5 2 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (movzx_r32_m16_effect_step 0x12591b 2 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125920 [0x66, 0x89, 0x14, 0x24] (StorePre 0x125920 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x125920 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x125920 4 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x125920 4 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_effect_step 0x125920 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125924 [0x0F, 0xB6, 0x54, 0x24, 0x1B] (LoadPre 0x125924 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x125924 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125924 5 2 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x125924 5 2 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (movzx_r32_m8_effect_step 0x125924 2 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125929 [0x88, 0x54, 0x24, 0x02] (StorePre 0x125929 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x125929 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125929 4 2 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125929 4 2 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_effect_step 0x125929 2 (by decide) (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x12592d [0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x12592d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x12592d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12592d 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x12592d 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x12592d 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x125931 [0x44, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x125931 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125931 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125931 8 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x125931 8 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_effect_step 0x125931 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125936 [0x48, 0x8B, 0x74, 0x24, 0x24] (LoadPre 0x125936 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125936 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125936 6 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125936 6 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x125936 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x12593b [0x48, 0x89, 0x74, 0x24, 0x60] (StorePre 0x12593b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12593b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12593b 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12593b 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x12593b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x125940 [0x48, 0x8B, 0x74, 0x24, 0x2C] (LoadPre 0x125940 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125940 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125940 6 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125940 6 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x125940 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x125945 [0x48, 0x89, 0x74, 0x24, 0x68] (StorePre 0x125945 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x125945 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125945 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125945 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x125945 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x12594a [0x48, 0x8B, 0x74, 0x24, 0x34] (LoadPre 0x12594a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x12594a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12594a 6 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12594a 6 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x12594a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x12594f [0x48, 0x89, 0x74, 0x24, 0x70] (StorePre 0x12594f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12594f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12594f 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12594f 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x12594f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125954 [0x8B, 0x74, 0x24, 0x3C] (LoadPre 0x125954 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125954 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125954 6 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x125954 6 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x125954 6 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x125958 [0x89, 0x74, 0x24, 0x78] (StorePre 0x125958 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x125958 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125958 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125958 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m32_r32_low_effect_step 0x125958 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x12595c [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x12595c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x12595c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12595c 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x12595c 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x12595c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x125961 [0x4C, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x125961 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x125961 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125961 9 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125961 9 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x125961 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x125966 [0x4C, 0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (StorePre 0x125966 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x125966 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125966 9 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125966 9 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_m64_r64_effect_step 0x125966 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x12596e [0x4C, 0x8B, 0x4C, 0x24, 0x48] (LoadPre 0x12596e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12596e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12596e 9 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x12596e 9 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x12596e 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (7, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125916) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (7, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12591b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (7, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125920) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (7, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125924) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 60), (3, 3), (4, 4), (7, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125929) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 60), (3, 3), (4, 4), (7, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12592d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (7, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125931) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125936) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 67), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12593b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 67), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125940) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 70), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125945) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 70), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12594a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 73), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12594f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 73), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125954) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 76), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125958) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 76), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12595c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125961) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 81), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125966) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 81), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12596e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f19 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 84), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125973) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l125912_1 code

theorem block_l125912 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125912 :=
  Rest.liftedBlock (rest_l125912 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125912 x hx)

theorem rest_l1259ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1259ed bytes_l1259ed) (entryMap (live .l1259ed))
      2 0x1259ed bytes_l1259ed b_l1259ed := by
  have f0 : InstrSpec 0x1259ed [0xB1, 0x02] (fun s => s.RIP = 0x1259ed) (movR8Imm8Effect 0x1259ed 2 1 0x2)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x1259ed 2 1 0x2).toInstrSpec (mov_r8_imm8_effect_step 0x1259ed 0xb1 (by decide) 0x2) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259ef) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x1259ef 0x1fd (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1259ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1259ed :=
  Rest.liftedBlock (rest_l1259ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1259ed x hx)

theorem rest_l1259f4_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x1259f4 bytes_l1259f4) [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 84), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]
      11 0x125a64 bytes_l1259f4_1 b_l1259f4_1 := by
  have f20 : InstrSpec 0x125a64 [0x66, 0x44, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x125a64 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125a64 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x125a64 9 9 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x125a64 9 9 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x125a64 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x125a6d [0x44, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x125a6d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125a6d + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x125a6d 9 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x125a6d 9 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r32_m32_effect_step 0x125a6d 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x125a75 [0x44, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x125a75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125a75 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x125a75 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x125a75 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_effect_step 0x125a75 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x125a7a [0x4C, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x125a7a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125a7a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125a7a 9 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125a7a 9 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x125a7a 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x125a82 [0x4C, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x125a82 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125a82 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125a82 9 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125a82 9 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x125a82 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x125a87 [0x4C, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x125a87 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125a87 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125a87 9 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125a87 9 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x125a87 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x125a8f [0x4C, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x125a8f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125a8f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125a8f 10 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x125a8f 10 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x125a8f 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x125a97 [0x4C, 0x89, 0x54, 0x24, 0x10] (StorePre 0x125a97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125a97 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125a97 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125a97 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x125a97 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x125a9c [0x4C, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x125a9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125a9c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125a9c 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125a9c 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x125a9c 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x125aa1 [0x41, 0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125aa1) (movR32Imm32Effect 0x125aa1 6 10 0x1)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x125aa1 6 10 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x125aa1 0x41 0xba (by decide) (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 84), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a6d) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 87), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a75) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 87), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a7a) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 90), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a82) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 90), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a87) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f25 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 93), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a8f) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f26 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 93), (10, 95), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a97) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 93), (10, 95), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a9c) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 93), (10, 95), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125aa1) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f29 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 93), (10, 99), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125aa7) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 101) (jmp_rel32_effect_step 0x125aa7 0x153 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l1259f4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1259f4 bytes_l1259f4) (entryMap (live .l1259f4))
      31 0x1259f4 bytes_l1259f4 b_l1259f4 := by
  have f0 : InstrSpec 0x1259f4 [0x8B, 0x7C, 0x24, 0x0C] (LoadPre 0x1259f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1259f4 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1259f4 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x1259f4 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x1259f4 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1259f8 [0x0F, 0xB6, 0x4C, 0x24, 0x10] (LoadPre 0x1259f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1259f8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1259f8 5 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1259f8 5 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m8_effect_step 0x1259f8 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1259fd [0x0F, 0xB7, 0x54, 0x24, 0x11] (LoadPre 0x1259fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x1259fd + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1259fd 5 2 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x1259fd 5 2 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m16_effect_step 0x1259fd 2 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125a02 [0x66, 0x89, 0x54, 0x24, 0x60] (StorePre 0x125a02 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125a02 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x125a02 5 2 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x125a02 5 2 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m16_r16_effect_step 0x125a02 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125a07 [0x0F, 0xB6, 0x54, 0x24, 0x13] (LoadPre 0x125a07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x125a07 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125a07 5 2 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x125a07 5 2 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m8_effect_step 0x125a07 2 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125a0c [0x88, 0x54, 0x24, 0x62] (StorePre 0x125a0c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x125a0c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125a0c 4 2 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125a0c 4 2 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (mov_m8_r8_effect_step 0x125a0c 2 (by decide) (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x125a10 [0x8B, 0x54, 0x24, 0x14] (LoadPre 0x125a10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125a10 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125a10 2 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x125a10 2 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x125a10 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x125a14 [0x44, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x125a14 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125a14 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125a14 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x125a14 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x125a14 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125a19 [0x48, 0x8B, 0x74, 0x24, 0x1C] (LoadPre 0x125a19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125a19 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125a19 6 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125a19 6 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x125a19 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x125a1e [0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x125a1e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125a1e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125a1e 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125a1e 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x125a1e 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x125a26 [0x48, 0x8B, 0x74, 0x24, 0x24] (LoadPre 0x125a26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125a26 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125a26 6 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125a26 6 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x125a26 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x125a2b [0x48, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x125a2b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125a2b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125a2b 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125a2b 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x125a2b 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x125a33 [0x48, 0x8B, 0x74, 0x24, 0x2C] (LoadPre 0x125a33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125a33 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125a33 6 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125a33 6 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x125a33 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x125a38 [0x48, 0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x125a38 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125a38 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125a38 6 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125a38 6 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x125a38 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125a40 [0x8B, 0x74, 0x24, 0x34] (LoadPre 0x125a40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125a40 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125a40 6 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x125a40 6 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x125a40 6 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x125a44 [0x89, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x125a44 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125a44 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x125a44 6 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125a44 6 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m32_r32_low_effect_step 0x125a44 6 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x125a4b [0x48, 0x8B, 0x74, 0x24, 0x38] (LoadPre 0x125a4b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x125a4b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125a4b 6 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125a4b 6 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x125a4b 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x125a50 [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x62] (LoadPre 0x125a50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x125a50 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125a50 6 9 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x125a50 6 9 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125a50 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x125a56 [0x44, 0x88, 0x8C, 0x24, 0xBA, 0x00, 0x00, 0x00] (StorePre 0x125a56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x125a56 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x125a56 8 9 (.sib 4 none 0 (.d32 0xba)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125a56 8 9 (.sib 4 none 0 (.d32 0xba))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125a56 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xba)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x125a5e [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x60] (LoadPre 0x125a5e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125a5e + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125a5e 6 9 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x125a5e 6 9 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x125a5e 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1259fd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a02) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a07) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 60), (3, 3), (4, 4), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a0c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 60), (3, 3), (4, 4), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a10) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (7, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a14) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a19) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 67), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a1e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 67), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a26) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 70), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a2b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 70), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a33) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 73), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a38) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 73), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a40) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 76), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a44) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 76), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a4b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a50) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 81), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a56) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 81), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a5e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f19 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 53), (8, 65), (9, 84), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125a64) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1259f4_1 code

theorem block_l1259f4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1259f4 :=
  Rest.liftedBlock (rest_l1259f4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1259f4 x hx)

theorem rest_l125aac [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125aac bytes_l125aac) (entryMap (live .l125aac))
      15 0x125aac bytes_l125aac b_l125aac := by
  have f0 : InstrSpec 0x125aac [0x8B, 0x8C, 0x24, 0xB4, 0x00, 0x00, 0x00] (LoadPre 0x125aac (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x125aac + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x125aac 1 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x125aac 1 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (mov_r32_m32_low_effect_step 0x125aac 1 (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125ab3 [0x89, 0x4C, 0x24, 0x44] (StorePre 0x125ab3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x125ab3 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125ab3 1 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125ab3 1 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_m32_r32_low_effect_step 0x125ab3 1 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x125ab7 [0x48, 0x8B, 0x8C, 0x24, 0xAC, 0x00, 0x00, 0x00] (LoadPre 0x125ab7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x125ab7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ab7 1 (.sib 4 none 0 (.d32 0xac)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x125ab7 1 (.sib 4 none 0 (.d32 0xac))).toInstrSpec (mov_r64_m64_effect_step 0x125ab7 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xac)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125abf [0x48, 0x89, 0x4C, 0x24, 0x3C] (StorePre 0x125abf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125abf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125abf 1 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125abf 1 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m64_r64_effect_step 0x125abf 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125ac4 [0x48, 0x8B, 0x8C, 0x24, 0xA4, 0x00, 0x00, 0x00] (LoadPre 0x125ac4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x125ac4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ac4 1 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x125ac4 1 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (mov_r64_m64_effect_step 0x125ac4 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125acc [0x48, 0x89, 0x4C, 0x24, 0x34] (StorePre 0x125acc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125acc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125acc 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125acc 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m64_r64_effect_step 0x125acc 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x125ad1 [0x48, 0x8B, 0x8C, 0x24, 0x94, 0x00, 0x00, 0x00] (LoadPre 0x125ad1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x125ad1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ad1 1 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x125ad1 1 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (mov_r64_m64_effect_step 0x125ad1 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x125ad9 [0x48, 0x8B, 0x94, 0x24, 0x9C, 0x00, 0x00, 0x00] (LoadPre 0x125ad9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x125ad9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ad9 2 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125ad9 2 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (mov_r64_m64_effect_step 0x125ad9 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125ae1 [0x48, 0x89, 0x54, 0x24, 0x2C] (StorePre 0x125ae1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125ae1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125ae1 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125ae1 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x125ae1 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x125ae6 [0x48, 0x89, 0x4C, 0x24, 0x24] (StorePre 0x125ae6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125ae6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125ae6 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125ae6 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x125ae6 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x125aeb [0x48, 0x8B, 0x8C, 0x24, 0xF0, 0x00, 0x00, 0x00] (LoadPre 0x125aeb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x125aeb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125aeb 1 (.sib 4 none 0 (.d32 0xf0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x125aeb 1 (.sib 4 none 0 (.d32 0xf0))).toInstrSpec (mov_r64_m64_effect_step 0x125aeb 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x125af3 [0x48, 0x8B, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00] (LoadPre 0x125af3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x125af3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125af3 2 (.sib 4 none 0 (.d32 0xf8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125af3 2 (.sib 4 none 0 (.d32 0xf8))).toInstrSpec (mov_r64_m64_effect_step 0x125af3 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x125afb [0x48, 0x89, 0x4C, 0x24, 0x14] (StorePre 0x125afb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125afb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125afb 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125afb 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x125afb 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x125b00 [0x48, 0x89, 0x54, 0x24, 0x1C] (StorePre 0x125b00 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125b00 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b00 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b00 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x125b00 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ab3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ab7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125abf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ac4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125acc) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ad1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ad9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ae1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ae6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125aeb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (2, 64), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125af3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125afb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b00) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 68), (2, 70), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b05) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 74) (jmp_rel8_effect_step 0x125b05 0x59 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125aac [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125aac :=
  Rest.liftedBlock (rest_l125aac code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125aac x hx)

theorem rest_l125b07 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125b07 bytes_l125b07) (entryMap (live .l125b07))
      14 0x125b07 bytes_l125b07 b_l125b07 := by
  have f0 : InstrSpec 0x125b07 [0x48, 0x8B, 0x8C, 0x24, 0x84, 0x00, 0x00, 0x00] (LoadPre 0x125b07 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x125b07 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b07 1 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x125b07 1 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_r64_m64_effect_step 0x125b07 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125b0f [0x48, 0x8B, 0x94, 0x24, 0x8C, 0x00, 0x00, 0x00] (LoadPre 0x125b0f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x125b0f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b0f 2 (.sib 4 none 0 (.d32 0x8c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125b0f 2 (.sib 4 none 0 (.d32 0x8c))).toInstrSpec (mov_r64_m64_effect_step 0x125b0f 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x8c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125b17 [0x48, 0x89, 0x54, 0x24, 0x1C] (StorePre 0x125b17 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125b17 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b17 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b17 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x125b17 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x125b1c [0x48, 0x8B, 0x94, 0x24, 0x94, 0x00, 0x00, 0x00] (LoadPre 0x125b1c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x125b1c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b1c 2 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125b1c 2 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (mov_r64_m64_effect_step 0x125b1c 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x125b24 [0x48, 0x89, 0x54, 0x24, 0x24] (StorePre 0x125b24 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125b24 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b24 2 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b24 2 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x125b24 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x125b29 [0x48, 0x8B, 0x94, 0x24, 0x9C, 0x00, 0x00, 0x00] (LoadPre 0x125b29 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x125b29 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b29 2 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125b29 2 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (mov_r64_m64_effect_step 0x125b29 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x125b31 [0x48, 0x89, 0x54, 0x24, 0x2C] (StorePre 0x125b31 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125b31 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b31 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b31 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x125b31 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x125b36 [0x48, 0x8B, 0x94, 0x24, 0xA4, 0x00, 0x00, 0x00] (LoadPre 0x125b36 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x125b36 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b36 2 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125b36 2 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (mov_r64_m64_effect_step 0x125b36 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125b3e [0x48, 0x89, 0x54, 0x24, 0x34] (StorePre 0x125b3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125b3e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b3e 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b3e 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m64_r64_effect_step 0x125b3e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x125b43 [0x48, 0x8B, 0x94, 0x24, 0xAC, 0x00, 0x00, 0x00] (LoadPre 0x125b43 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x125b43 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125b43 2 (.sib 4 none 0 (.d32 0xac)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x125b43 2 (.sib 4 none 0 (.d32 0xac))).toInstrSpec (mov_r64_m64_effect_step 0x125b43 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xac)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x125b4b [0x48, 0x89, 0x54, 0x24, 0x3C] (StorePre 0x125b4b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125b4b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b4b 2 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b4b 2 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m64_r64_effect_step 0x125b4b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x125b50 [0x8B, 0x94, 0x24, 0xB4, 0x00, 0x00, 0x00] (LoadPre 0x125b50 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x125b50 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x125b50 2 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x125b50 2 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (mov_r32_m32_low_effect_step 0x125b50 2 (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x125b57 [0x89, 0x54, 0x24, 0x44] (StorePre 0x125b57 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x125b57 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125b57 2 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125b57 2 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_m32_r32_low_effect_step 0x125b57 2 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x125b5b [0x48, 0x89, 0x4C, 0x24, 0x14] (StorePre 0x125b5b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125b5b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b5b 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b5b 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m64_r64_effect_step 0x125b5b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b0f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b17) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b1c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b24) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b29) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b31) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b36) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b3e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b43) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b4b) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b50) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b57) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b5b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b60) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 74) (by decide) rfl

theorem block_l125b07 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125b07 :=
  Rest.liftedBlock (rest_l125b07 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125b07 x hx)

theorem rest_l125b60_1 [Bindings] (code : CodeMap) :
    Rest (n := 86) code lifted (codeRange 0x125b60 bytes_l125b60) [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 84), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]
      10 0x125bc1 bytes_l125b60_1 b_l125b60_1 := by
  have f20 : InstrSpec 0x125bc1 [0x66, 0x89, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x125bc1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125bc1 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x125bc1 8 7 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x125bc1 8 7 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m16_r16_effect_step 0x125bc1 7 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x125bc9 [0x8B, 0x7C, 0x24, 0x78] (LoadPre 0x125bc9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x125bc9 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125bc9 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x125bc9 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r32_m32_low_effect_step 0x125bc9 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x125bcd [0x89, 0x7C, 0x24, 0x20] (StorePre 0x125bcd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125bcd + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125bcd 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125bcd 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_low_effect_step 0x125bcd 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x125bd1 [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x125bd1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x125bd1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125bd1 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125bd1 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x125bd1 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x125bd6 [0x48, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x125bd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125bd6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125bd6 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125bd6 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x125bd6 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x125bdb [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x125bdb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125bdb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125bdb 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x125bdb 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x125bdb 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x125be0 [0x4C, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x125be0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x125be0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125be0 8 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x125be0 8 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x125be0 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x125be5 [0x4C, 0x89, 0x44, 0x24, 0x10] (StorePre 0x125be5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125be5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125be5 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125be5 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x125be5 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x125bea [0x48, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x125bea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125bea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125bea 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125bea 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x125bea 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x125bef [0x89, 0xC5] (fun s => s.RIP = 0x125bef) (movR32R32Effect 0x125bef 2 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x125bef 2 5 0).toInstrSpec (mov_r32_r32_effect_step 0x125bef 0xc5 (by decide)) pre_rip
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 84), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bc9) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 87), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bcd) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 87), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bd1) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 90), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bd6) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 90), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bdb) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f25 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 93), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125be0) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 93), (8, 95), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125be5) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 93), (8, 95), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bea) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 93), (8, 95), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bef) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f29 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (5, 99), (6, 79), (7, 93), (8, 95), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bf1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 101) (by decide) rfl

theorem rest_l125b60 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125b60 bytes_l125b60) (entryMap (live .l125b60))
      30 0x125b60 bytes_l125b60 b_l125b60 := by
  have f0 : InstrSpec 0x125b60 [0x44, 0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x125b60 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x125b60 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125b60 9 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x125b60 9 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_effect_step 0x125b60 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125b65 [0x0F, 0xB6, 0x4C, 0x24, 0x18] (LoadPre 0x125b65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125b65 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125b65 5 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x125b65 5 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x125b65 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x125b6a [0x0F, 0xB7, 0x54, 0x24, 0x19] (LoadPre 0x125b6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x125b6a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x125b6a 5 2 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x125b6a 5 2 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (movzx_r32_m16_effect_step 0x125b6a 2 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125b6f [0x66, 0x89, 0x14, 0x24] (StorePre 0x125b6f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x125b6f + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x125b6f 4 2 (.sib 4 none 0 .none))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x125b6f 4 2 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_effect_step 0x125b6f 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125b73 [0x0F, 0xB6, 0x54, 0x24, 0x1B] (LoadPre 0x125b73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x125b73 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125b73 5 2 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x125b73 5 2 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (movzx_r32_m8_effect_step 0x125b73 2 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125b78 [0x88, 0x54, 0x24, 0x02] (StorePre 0x125b78 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x125b78 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125b78 4 2 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125b78 4 2 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_effect_step 0x125b78 2 (by decide) (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x125b7c [0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x125b7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x125b7c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125b7c 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x125b7c 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x125b7c 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x125b80 [0x44, 0x8B, 0x5C, 0x24, 0x20] (LoadPre 0x125b80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125b80 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x125b80 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x125b80 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_effect_step 0x125b80 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x125b85 [0x48, 0x8B, 0x74, 0x24, 0x24] (LoadPre 0x125b85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x125b85 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125b85 6 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125b85 6 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x125b85 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x125b8a [0x48, 0x89, 0x74, 0x24, 0x60] (StorePre 0x125b8a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x125b8a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b8a 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b8a 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x125b8a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x125b8f [0x48, 0x8B, 0x74, 0x24, 0x2C] (LoadPre 0x125b8f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x125b8f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125b8f 6 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125b8f 6 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x125b8f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x125b94 [0x48, 0x89, 0x74, 0x24, 0x68] (StorePre 0x125b94 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x125b94 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b94 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b94 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x125b94 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x125b99 [0x48, 0x8B, 0x74, 0x24, 0x34] (LoadPre 0x125b99 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x125b99 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125b99 6 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125b99 6 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x125b99 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x125b9e [0x48, 0x89, 0x74, 0x24, 0x70] (StorePre 0x125b9e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x125b9e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125b9e 6 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125b9e 6 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x125b9e 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125ba3 [0x8B, 0x74, 0x24, 0x3C] (LoadPre 0x125ba3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x125ba3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125ba3 6 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x125ba3 6 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x125ba3 6 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x125ba7 [0x89, 0x74, 0x24, 0x78] (StorePre 0x125ba7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x125ba7 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x125ba7 6 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125ba7 6 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m32_r32_low_effect_step 0x125ba7 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x125bab [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x125bab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x125bab + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125bab 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x125bab 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x125bab 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x125bb0 [0x0F, 0xB6, 0x7C, 0x24, 0x02] (LoadPre 0x125bb0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x125bb0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x125bb0 5 7 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x125bb0 5 7 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m8_effect_step 0x125bb0 7 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x125bb5 [0x40, 0x88, 0xBC, 0x24, 0xBA, 0x00, 0x00, 0x00] (StorePre 0x125bb5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x125bb5 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x125bb5 8 7 (.sib 4 none 0 (.d32 0xba)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125bb5 8 7 (.sib 4 none 0 (.d32 0xba))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125bb5 0x40 (by decide) 7 (.sib 4 none 0 (.d32 0xba)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x125bbd [0x0F, 0xB7, 0x3C, 0x24] (LoadPre 0x125bbd (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x125bbd + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x125bbd 4 7 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x125bbd 4 7 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x125bbd 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (9, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b65) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (9, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b6a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (9, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b6f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 55), (2, 57), (3, 3), (4, 4), (9, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b73) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 55), (2, 60), (3, 3), (4, 4), (9, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b78) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 60), (3, 3), (4, 4), (9, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b7c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (9, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b80) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b85) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 67), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b8a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 67), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b8f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 70), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b94) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 70), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b99) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 73), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125b9e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 73), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ba3) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 76), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ba7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 76), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bab) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bb0) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 81), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bb5) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 81), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bbd) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 55), (2, 63), (3, 3), (4, 4), (6, 79), (7, 84), (9, 53), (11, 65), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bc1) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l125b60_1 code

theorem block_l125b60 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125b60 :=
  Rest.liftedBlock (rest_l125b60 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125b60 x hx)

theorem rest_l125bf1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125bf1 bytes_l125bf1) (entryMap (live .l125bf1))
      4 0x125bf1 bytes_l125bf1 b_l125bf1 := by
  have f0 : InstrSpec 0x125bf1 [0x41, 0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x125bf1) (movR32Imm32Effect 0x125bf1 6 10 0x1)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x125bf1 6 10 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x125bf1 0x41 0xba (by decide) (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x125bf7 [0x89, 0xE8] (fun s => s.RIP = 0x125bf7) (movR32R32Effect 0x125bf7 2 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x125bf7 2 0 5).toInstrSpec (mov_r32_r32_effect_step 0x125bf7 0xe8 (by decide)) pre_rip
  have f2 : InstrSpec 0x125bf9 [0x44, 0x89, 0xCF] (fun s => s.RIP = 0x125bf9) (movR32R32Effect 0x125bf9 3 7 9)
      [.gpr 9] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x125bf9 3 7 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x125bf9 0x44 0xcf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x125bfc [0x45, 0x89, 0xD8] (fun s => s.RIP = 0x125bfc) (movR32R32Effect 0x125bfc 3 8 11)
      [.gpr 11] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x125bfc 3 8 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x125bfc 0x45 0xd8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bf7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bf9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bfc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 59), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125bff) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l125bf1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125bf1 :=
  Rest.liftedBlock (rest_l125bf1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125bf1 x hx)

theorem rest_l125bff_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x125bff bytes_l125bff) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 79), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]
      16 0x125c81 bytes_l125bff_1 b_l125bff_1 := by
  have f20 : InstrSpec 0x125c81 [0x44, 0x8B, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x125c81 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125c81 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x125c81 9 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x125c81 9 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r32_m32_effect_step 0x125c81 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x125c89 [0x44, 0x89, 0x4B, 0x34] (StorePre 0x125c89 4 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x125c89 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x125c89 9 (.base 3 (.d8 0x34)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x125c89 9 (.base 3 (.d8 0x34))).toInstrSpec (mov_m32_r32_effect_step 0x125c89 0x44 (by decide) 1 (.base 3 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x125c8d [0x89, 0x43, 0x08] (StorePre 0x125c8d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x125c8d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125c8d 0 (.base 3 (.d8 0x8)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125c8d 0 (.base 3 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x125c8d 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x125c90 [0x89, 0x7B, 0x0C] (StorePre 0x125c90 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x125c90 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125c90 7 (.base 3 (.d8 0xc)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125c90 7 (.base 3 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x125c90 7 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x125c93 [0x88, 0x4B, 0x10] (StorePre 0x125c93 3 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x125c93 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x125c93 3 1 (.base 3 (.d8 0x10)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x125c93 3 1 (.base 3 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x125c93 1 (by decide) (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x125c96 [0x89, 0x53, 0x14] (StorePre 0x125c96 3 (fun s => AddrMode.addr (.base 3 (.d8 0x14)) s (0x125c96 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x125c96 2 (.base 3 (.d8 0x14)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125c96 2 (.base 3 (.d8 0x14))).toInstrSpec (mov_m32_r32_low_effect_step 0x125c96 2 (.base 3 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x125c99 [0x44, 0x89, 0x43, 0x18] (StorePre 0x125c99 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x125c99 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x125c99 8 (.base 3 (.d8 0x18)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x125c99 8 (.base 3 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x125c99 0x44 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x125c9d [0x48, 0x89, 0x73, 0x38] (StorePre 0x125c9d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x125c9d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125c9d 6 (.base 3 (.d8 0x38)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125c9d 6 (.base 3 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x125c9d 0x48 (by decide) 6 (.base 3 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x125ca1 [0x4C, 0x89, 0x13] (StorePre 0x125ca1 3 (fun s => AddrMode.addr (.base 3 .none) s (0x125ca1 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x125ca1 10 (.base 3 .none))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125ca1 10 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x125ca1 0x4c (by decide) 2 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x125ca4 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x125ca4) (movR64R64Effect 0x125ca4 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x125ca4 0 3).toInstrSpec (mov_r64_r64_effect_step 0x125ca4 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x125ca7 [0x48, 0x81, 0xC4, 0x38, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x125ca7) (addR64Imm32Effect 0x125ca7 4 0x138)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x125ca7 4 0x138).toInstrSpec (add_r64_imm32_effect_step 0x125ca7 0x48 0xc4 0x138 (by decide) (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x125cae [0x5B] (PopPre 0x125cae) (popR64Effect 0x125cae 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x125cae 1 3).toInstrSpec (pop_r64_effect_step 0x125cae 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f32 : InstrSpec 0x125caf [0x41, 0x5E] (PopPre 0x125caf) (popR64Effect 0x125caf 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x125caf 2 14).toInstrSpec (pop_r64_rex_effect_step 0x125caf 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f33 : InstrSpec 0x125cb1 [0x41, 0x5F] (PopPre 0x125cb1) (popR64Effect 0x125cb1 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x125cb1 2 15).toInstrSpec (pop_r64_rex_effect_step 0x125cb1 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f34 : InstrSpec 0x125cb3 [0x5D] (PopPre 0x125cb3) (popR64Effect 0x125cb3 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x125cb3 1 5).toInstrSpec (pop_r64_effect_step 0x125cb3 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f35 : InstrSpec 0x125cb4 [0xC3] (RetPre 0x125cb4) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x125cb4).toInstrSpec (ret_effect_step 0x125cb4) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f20 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c89) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c8d) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c90) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c93) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c96) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c99) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c9d) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ca1) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ca4) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 92), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ca7) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f30 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 92), (1, 1), (2, 2), (3, 3), (4, 94), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cae) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f31 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 97) f31 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 98) (ρ' := [(0, 92), (1, 1), (2, 2), (3, 96), (4, 97), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125caf) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f32 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f32 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 92), (1, 1), (2, 2), (3, 96), (4, 100), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 99), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cb1) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f33 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 103) f33 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 92), (1, 1), (2, 2), (3, 96), (4, 103), (5, 68), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cb3) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f34 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 106) f34 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 107) (ρ' := [(0, 92), (1, 1), (2, 2), (3, 96), (4, 106), (5, 105), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cb4) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f35 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 109) f35 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 110) (ρ' := [(0, 92), (1, 1), (2, 2), (3, 96), (4, 109), (5, 105), (6, 6), (7, 7), (8, 8), (9, 82), (10, 10), (11, 75), (12, 12), (13, 13), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)]) f35 (by decide) rfl rfl rfl (by decide)

theorem rest_l125bff [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125bff bytes_l125bff) (entryMap (live .l125bff))
      36 0x125bff bytes_l125bff b_l125bff := by
  have f0 : InstrSpec 0x125bff [0x44, 0x0F, 0xB7, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x125bff (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125bff + BitVec.ofNat 64 9)) 2) (movzxR32M16Effect 0x125bff 9 9 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x125bff 9 9 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x125bff 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125c08 [0x66, 0x44, 0x89, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x125c08 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x125c08 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x125c08 9 9 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x125c08 9 9 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x125c08 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x125c11 [0x44, 0x0F, 0xB6, 0x9C, 0x24, 0xBA, 0x00, 0x00, 0x00] (LoadPre 0x125c11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x125c11 + BitVec.ofNat 64 9)) 1) (movzxR32M8Effect 0x125c11 9 11 (.sib 4 none 0 (.d32 0xba)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x125c11 9 11 (.sib 4 none 0 (.d32 0xba))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125c11 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0xba)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125c1a [0x44, 0x88, 0x9C, 0x24, 0xCA, 0x00, 0x00, 0x00] (StorePre 0x125c1a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x125c1a + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x125c1a 8 11 (.sib 4 none 0 (.d32 0xca)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125c1a 8 11 (.sib 4 none 0 (.d32 0xca))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125c1a 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0xca)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125c22 [0x4C, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x125c22 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125c22 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125c22 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x125c22 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x125c22 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125c27 [0x4C, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x125c27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125c27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125c27 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x125c27 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x125c27 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x125c2c [0x4C, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x125c2c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125c2c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125c2c 14 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125c2c 14 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x125c2c 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x125c34 [0x4C, 0x89, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x125c34 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125c34 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125c34 15 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125c34 15 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x125c34 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x125c3c [0x4C, 0x8B, 0x74, 0x24, 0x18] (LoadPre 0x125c3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125c3c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x125c3c 14 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x125c3c 14 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x125c3c 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x125c41 [0x4C, 0x89, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x125c41 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125c41 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x125c41 14 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125c41 14 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x125c41 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x125c49 [0x8B, 0x6C, 0x24, 0x20] (LoadPre 0x125c49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125c49 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x125c49 5 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x125c49 5 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x125c49 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x125c4d [0x89, 0xAC, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x125c4d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x125c4d + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x125c4d 5 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x125c4d 5 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m32_r32_low_effect_step 0x125c4d 5 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x125c54 [0x44, 0x88, 0x5B, 0x13] (StorePre 0x125c54 4 (fun s => AddrMode.addr (.base 3 (.d8 0x13)) s (0x125c54 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x125c54 4 11 (.base 3 (.d8 0x13)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x125c54 4 11 (.base 3 (.d8 0x13))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125c54 0x44 (by decide) 3 (.base 3 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x125c58 [0x66, 0x44, 0x89, 0x4B, 0x11] (StorePre 0x125c58 5 (fun s => AddrMode.addr (.base 3 (.d8 0x11)) s (0x125c58 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x125c58 5 9 (.base 3 (.d8 0x11)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM16R16Effect_footprint 0x125c58 5 9 (.base 3 (.d8 0x11))).toInstrSpec (mov_m16_r16_rex_effect_step 0x125c58 0x44 (by decide) 1 (.base 3 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125c5d [0x4C, 0x8B, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x125c5d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x125c5d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125c5d 9 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125c5d 9 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x125c5d 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x125c65 [0x4C, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x125c65 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x125c65 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125c65 11 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x125c65 11 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x125c65 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x125c6d [0x4C, 0x89, 0x4B, 0x1C] (StorePre 0x125c6d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x125c6d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125c6d 9 (.base 3 (.d8 0x1c)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125c6d 9 (.base 3 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x125c6d 0x4c (by decide) 1 (.base 3 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x125c71 [0x4C, 0x89, 0x5B, 0x24] (StorePre 0x125c71 4 (fun s => AddrMode.addr (.base 3 (.d8 0x24)) s (0x125c71 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125c71 11 (.base 3 (.d8 0x24)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125c71 11 (.base 3 (.d8 0x24))).toInstrSpec (mov_m64_r64_effect_step 0x125c71 0x4c (by decide) 3 (.base 3 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x125c75 [0x4C, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x125c75 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x125c75 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125c75 9 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125c75 9 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x125c75 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x125c7d [0x4C, 0x89, 0x4B, 0x2C] (StorePre 0x125c7d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x125c7d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125c7d 9 (.base 3 (.d8 0x2c)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125c7d 9 (.base 3 (.d8 0x2c))).toInstrSpec (mov_m64_r64_effect_step 0x125c7d 0x4c (by decide) 1 (.base 3 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c08) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c11) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c1a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c22) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c27) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 59), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c2c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 59), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c34) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 59), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c3c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c41) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c49) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c4d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c54) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c58) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 53), (10, 10), (11, 56), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c5d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 73), (10, 10), (11, 56), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c65) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 73), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c6d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 73), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c71) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 73), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c75) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f18 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 79), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c7d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 68), (6, 6), (7, 7), (8, 8), (9, 79), (10, 10), (11, 75), (12, 12), (13, 13), (14, 65), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125c81) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l125bff_1 code

theorem block_l125bff [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125bff :=
  Rest.liftedBlock (rest_l125bff code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125bff x hx)

theorem rest_l125cb5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125cb5 bytes_l125cb5) (entryMap (live .l125cb5))
      3 0x125cb5 bytes_l125cb5 b_l125cb5 := by
  have f0 : InstrSpec 0x125cb5 [0x44, 0x8B, 0x9C, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x125cb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x125cb5 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x125cb5 11 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x125cb5 11 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r32_m32_effect_step 0x125cb5 0x44 (by decide) 3 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125cbd [0x45, 0x29, 0xCB] (fun s => s.RIP = 0x125cbd) (subR32R32Effect 0x125cbd 3 11 9)
      [.gpr 11, .gpr 9] [] [.reg 11, .flags, .rip] :=
    (subR32R32Effect_footprint 0x125cbd 3 11 9).toInstrSpec (sub_r32_r32_rex_effect_step 0x125cbd 0x45 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cbd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.out (n := 57) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 55), (12, 12), (13, 13), (16, 56), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cc0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x125cc0 6 0xa) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l125cb5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125cb5 :=
  Rest.liftedBlock (rest_l125cb5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125cb5 x hx)

theorem rest_l125cc2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125cc2 bytes_l125cc2) (entryMap (live .l125cc2))
      3 0x125cc2 bytes_l125cc2 b_l125cc2 := by
  have f0 : InstrSpec 0x125cc2 [0xB1, 0x13] (fun s => s.RIP = 0x125cc2) (movR8Imm8Effect 0x125cc2 2 1 0x13)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR8Imm8Effect_footprint 0x125cc2 2 1 0x13).toInstrSpec (mov_r8_imm8_effect_step 0x125cc2 0xb1 (by decide) 0x13) pre_rip
  have f1 : InstrSpec 0x125cc4 [0x44, 0x89, 0xCA] (fun s => s.RIP = 0x125cc4) (movR32R32Effect 0x125cc4 3 2 9)
      [.gpr 9] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x125cc4 3 2 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x125cc4 0x44 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cc4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cc7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 57) (jmp_rel32_effect_step 0x125cc7 0xffffff25 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125cc2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125cc2 :=
  Rest.liftedBlock (rest_l125cc2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125cc2 x hx)

theorem rest_l125ccc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x125ccc bytes_l125ccc) (entryMap (live .l125ccc))
      20 0x125ccc bytes_l125ccc b_l125ccc := by
  have f0 : InstrSpec 0x125ccc [0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x06] (LoadPre 0x125ccc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x125ccc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x125ccc 6 9 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M8Effect_footprint 0x125ccc 6 9 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x125ccc 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x125cd2 [0x44, 0x88, 0x8C, 0x24, 0xBA, 0x00, 0x00, 0x00] (StorePre 0x125cd2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x125cd2 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x125cd2 8 9 (.sib 4 none 0 (.d32 0xba)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x125cd2 8 9 (.sib 4 none 0 (.d32 0xba))).toInstrSpec (mov_m8_r8_rex_effect_step 0x125cd2 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xba)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x125cda [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x04] (LoadPre 0x125cda (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x125cda + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x125cda 6 9 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x125cda 6 9 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x125cda 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x125ce0 [0x66, 0x44, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x125ce0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x125ce0 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x125ce0 9 9 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x125ce0 9 9 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x125ce0 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x125ce9 [0x4C, 0x8B, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x125ce9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x125ce9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125ce9 9 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125ce9 9 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (mov_r64_m64_effect_step 0x125ce9 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x125cf1 [0x4C, 0x8B, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00] (LoadPre 0x125cf1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x125cf1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125cf1 10 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x125cf1 10 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (mov_r64_m64_effect_step 0x125cf1 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x125cf9 [0x4C, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x125cf9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x125cf9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125cf9 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125cf9 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x125cf9 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x125cfe [0x4C, 0x89, 0x54, 0x24, 0x10] (StorePre 0x125cfe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x125cfe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125cfe 10 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125cfe 10 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x125cfe 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x125d03 [0x4C, 0x8B, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x125d03 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x125d03 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125d03 9 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125d03 9 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (mov_r64_m64_effect_step 0x125d03 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x125d0b [0x4C, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x125d0b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x125d0b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x125d0b 9 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x125d0b 9 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x125d0b 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x125d10 [0x44, 0x8B, 0x8C, 0x24, 0x18, 0x01, 0x00, 0x00] (LoadPre 0x125d10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x125d10 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x125d10 9 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x125d10 9 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_r32_m32_effect_step 0x125d10 0x44 (by decide) 1 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x125d18 [0x44, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x125d18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x125d18 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x125d18 9 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x125d18 9 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_effect_step 0x125d18 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x125d1d [0x4C, 0x8B, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x125d1d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x125d1d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125d1d 9 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125d1d 9 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_r64_m64_effect_step 0x125d1d 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x125d25 [0x4C, 0x89, 0x4B, 0x50] (StorePre 0x125d25 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x125d25 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125d25 9 (.base 3 (.d8 0x50)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125d25 9 (.base 3 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x125d25 0x4c (by decide) 1 (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x125d29 [0x4C, 0x8B, 0x8C, 0x24, 0x20, 0x01, 0x00, 0x00] (LoadPre 0x125d29 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x125d29 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125d29 9 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x125d29 9 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_r64_m64_effect_step 0x125d29 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x125d31 [0x4C, 0x8B, 0x94, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x125d31 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x125d31 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x125d31 10 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x125d31 10 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_r64_m64_effect_step 0x125d31 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x125d39 [0x4C, 0x89, 0x53, 0x48] (StorePre 0x125d39 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x125d39 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125d39 10 (.base 3 (.d8 0x48)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125d39 10 (.base 3 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x125d39 0x4c (by decide) 2 (.base 3 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x125d3d [0x4C, 0x89, 0x4B, 0x40] (StorePre 0x125d3d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x125d3d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x125d3d 9 (.base 3 (.d8 0x40)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x125d3d 9 (.base 3 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x125d3d 0x4c (by decide) 1 (.base 3 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x125d41 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x125d41) (xorR32R32Effect 0x125d41 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x125d41 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x125d41 0x45 0xd2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cd2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cda) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 56), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ce0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 56), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125ce9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cf1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cf9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125cfe) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d03) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 65), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d0b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 65), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d10) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 68), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d18) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 68), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d1d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d25) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d29) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 74), (10, 61), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d31) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 74), (10, 76), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d39) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 74), (10, 76), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d3d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 74), (10, 76), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d41) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 74), (10, 80), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x125d44) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 82) (jmp_rel32_effect_step 0x125d44 0xfffffeb6 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l125ccc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l125ccc :=
  Rest.liftedBlock (rest_l125ccc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l125ccc x hx)

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

theorem_by block_l125760_eval :
    program.runBlock (dialect code) ⟨.l125760, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125765_eval :
    program.runBlock (dialect code) ⟨.l125765, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12576f_eval :
    program.runBlock (dialect code) ⟨.l12576f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125788_eval :
    program.runBlock (dialect code) ⟨.l125788, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1257aa_eval :
    program.runBlock (dialect code) ⟨.l1257aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1257b7_eval :
    program.runBlock (dialect code) ⟨.l1257b7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125877_eval :
    program.runBlock (dialect code) ⟨.l125877, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1258a7_eval :
    program.runBlock (dialect code) ⟨.l1258a7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1258d9_eval :
    program.runBlock (dialect code) ⟨.l1258d9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1258e9_eval :
    program.runBlock (dialect code) ⟨.l1258e9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125903_eval :
    program.runBlock (dialect code) ⟨.l125903, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125912_eval :
    program.runBlock (dialect code) ⟨.l125912, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1259ed_eval :
    program.runBlock (dialect code) ⟨.l1259ed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1259f4_eval :
    program.runBlock (dialect code) ⟨.l1259f4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125aac_eval :
    program.runBlock (dialect code) ⟨.l125aac, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125b07_eval :
    program.runBlock (dialect code) ⟨.l125b07, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125b60_eval :
    program.runBlock (dialect code) ⟨.l125b60, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125bf1_eval :
    program.runBlock (dialect code) ⟨.l125bf1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125bff_eval :
    program.runBlock (dialect code) ⟨.l125bff, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125cb5_eval :
    program.runBlock (dialect code) ⟨.l125cb5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125cc2_eval :
    program.runBlock (dialect code) ⟨.l125cc2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l125ccc_eval :
    program.runBlock (dialect code) ⟨.l125ccc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
