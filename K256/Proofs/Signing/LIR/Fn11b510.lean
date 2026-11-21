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

theorem rest_l11b510 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11b510 bytes_l11b510) (entryMap (live .l11b510))
      12 0x11b510 bytes_l11b510 b_l11b510 := by
  have f0 : InstrSpec 0x11b510 [0x55] (PushPre 0x11b510 1) (pushR64Effect 0x11b510 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b510 1 5).toInstrSpec (push_r64_effect_step 0x11b510 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x11b511 [0x41, 0x57] (PushPre 0x11b511 2) (pushR64Effect 0x11b511 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b511 2 15).toInstrSpec (push_r64_rex_effect_step 0x11b511 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x11b513 [0x41, 0x56] (PushPre 0x11b513 2) (pushR64Effect 0x11b513 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b513 2 14).toInstrSpec (push_r64_rex_effect_step 0x11b513 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x11b515 [0x41, 0x55] (PushPre 0x11b515 2) (pushR64Effect 0x11b515 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b515 2 13).toInstrSpec (push_r64_rex_effect_step 0x11b515 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x11b517 [0x41, 0x54] (PushPre 0x11b517 2) (pushR64Effect 0x11b517 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b517 2 12).toInstrSpec (push_r64_rex_effect_step 0x11b517 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x11b519 [0x53] (PushPre 0x11b519 1) (pushR64Effect 0x11b519 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11b519 1 3).toInstrSpec (push_r64_effect_step 0x11b519 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x11b51a [0x48, 0x83, 0xEC, 0x48] (fun s => s.RIP = 0x11b51a) (subR64Imm8Effect 0x11b51a 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x11b51a 4 0x48).toInstrSpec (sub_r64_imm8_effect_step 0x11b51a 0x48 0xec 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11b51e [0x48, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x11b51e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11b51e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b51e 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b51e 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x11b51e 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x11b523 [0x48, 0xBF, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC, 0xAE, 0xBA] (fun s => s.RIP = 0x11b523) (movR64Imm64Effect 0x11b523 7 0xbaaedce6af48a03b)
      [] [] [.reg 7, .rip] :=
    (movR64Imm64Effect_footprint 0x11b523 7 0xbaaedce6af48a03b).toInstrSpec (mov_r64_imm64_effect_step 0x11b523 0x48 0xbf (by decide) (by decide) 0xbaaedce6af48a03b) pre_rip
  have f9 : InstrSpec 0x11b52d [0x49, 0xB9, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40] (fun s => s.RIP = 0x11b52d) (movR64Imm64Effect 0x11b52d 9 0x402da1732fc9bebf)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x11b52d 9 0x402da1732fc9bebf).toInstrSpec (mov_r64_imm64_effect_step 0x11b52d 0x49 0xb9 (by decide) (by decide) 0x402da1732fc9bebf) pre_rip
  have f10 : InstrSpec 0x11b537 [0x85, 0xD2] (fun s => s.RIP = 0x11b537) (testR32R32Effect 0x11b537 2 2 2)
      [.gpr 2, .gpr 2] [] [.flags, .rip] :=
    (testR32R32Effect_footprint 0x11b537 2 2 2).toInstrSpec (test_r32_r32_effect_step 0x11b537 0xd2 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b511) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b513) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b515) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b517) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b519) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b51a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b51e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b523) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 68), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b52d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 68), (9, 70), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b537) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 68), (9, 70), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b539) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 74) (jcc_rel8_effect_step 0x11b539 4 0x68) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11b510 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11b510 :=
  Rest.liftedBlock (rest_l11b510 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11b510 x hx)

theorem rest_l11b53b_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x11b53b bytes_l11b53b) [(1, 81), (2, 73), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x11b59e bytes_l11b53b_1 b_l11b53b_1 := by
  have f20 : InstrSpec 0x11b59e [0x49, 0xFF, 0xC1] (fun s => s.RIP = 0x11b59e) (incR64Effect 0x11b59e 9)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (incR64Effect_footprint 0x11b59e 9).toInstrSpec (inc_r64_effect_step 0x11b59e 0x49 0xc1 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f20 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 81), (2, 73), (4, 4), (6, 6), (7, 61), (9, 85), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5a1) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 87) (jmp_rel8_effect_step 0x11b5a1 0x17 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l11b53b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11b53b bytes_l11b53b) (entryMap (live .l11b53b))
      22 0x11b53b bytes_l11b53b b_l11b53b := by
  have f0 : InstrSpec 0x11b53b [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11b53b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b53b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b53b (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11b53b (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11b53b 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11b544 [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x11b544) (leaR64Effect 0x11b544 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11b544 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x11b544 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11b549 [0x31, 0xC9] (fun s => s.RIP = 0x11b549) (xorR32R32Effect 0x11b549 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b549 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x11b549 0xc9 (by decide)) pre_rip
  have f3 : InstrSpec 0x11b54b [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x11b54b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b54b + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b54b 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11b54b 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11b54b 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11b550 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x11b550) (sarR64Effect 0x11b550 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x11b550 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x11b550 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11b554 [0x48, 0x01, 0xCF] (fun s => s.RIP = 0x11b554) (addR64R64Effect 0x11b554 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b554 7 1).toInstrSpec (add_r64_r64_effect_step 0x11b554 0x48 0xcf (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11b557 [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x11b557 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11b557 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b557 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b557 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x11b557 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x11b55c [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11b55c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b55c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b55c (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11b55c (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11b55c 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x11b565 [0x31, 0xD2] (fun s => s.RIP = 0x11b565) (xorR32R32Effect 0x11b565 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b565 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x11b565 0xd2 (by decide)) pre_rip
  have f9 : InstrSpec 0x11b567 [0x48, 0x2B, 0x54, 0x24, 0x08] (LoadPre 0x11b567 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b567 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b567 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11b567 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11b567 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x11b56c [0x31, 0xC9] (fun s => s.RIP = 0x11b56c) (xorR32R32Effect 0x11b56c 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b56c 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x11b56c 0xc9 (by decide)) pre_rip
  have f11 : InstrSpec 0x11b56e [0x48, 0xC1, 0xFA, 0x3F] (fun s => s.RIP = 0x11b56e) (sarR64Effect 0x11b56e 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (sarR64Effect_footprint 0x11b56e 4 2 63).toInstrSpec (sar_r64_imm8_effect_step 0x11b56e 0x48 0xfa 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11b572 [0x48, 0x83, 0xC2, 0xFE] (fun s => s.RIP = 0x11b572) (addR64Imm8Effect 0x11b572 2 0xfe)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11b572 2 0xfe).toInstrSpec (add_r64_imm8_effect_step 0x11b572 0x48 0xc2 0xfe (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11b576 [0x48, 0x89, 0x54, 0x24, 0x30] (StorePre 0x11b576 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11b576 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b576 2 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b576 2 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x11b576 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x11b57b [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11b57b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b57b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b57b (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11b57b (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11b57b 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x11b584 [0x48, 0x2B, 0x4C, 0x24, 0x08] (LoadPre 0x11b584 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b584 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b584 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11b584 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11b584 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x11b589 [0x48, 0xC1, 0xF9, 0x3F] (fun s => s.RIP = 0x11b589) (sarR64Effect 0x11b589 4 1 63)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR64Effect_footprint 0x11b589 4 1 63).toInstrSpec (sar_r64_imm8_effect_step 0x11b589 0x48 0xf9 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11b58d [0x48, 0xFF, 0xC9] (fun s => s.RIP = 0x11b58d) (decR64Effect 0x11b58d 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (decR64Effect_footprint 0x11b58d 1).toInstrSpec (dec_r64_effect_step 0x11b58d 0x48 0xc9 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11b590 [0x48, 0x89, 0x4C, 0x24, 0x18] (StorePre 0x11b590 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b590 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b590 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b590 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11b590 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11b595 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11b595 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b595 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b595 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11b595 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11b595 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b544) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b549) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b54b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 57), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b550) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b554) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 2), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b557) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(1, 59), (2, 2), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b55c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(1, 59), (2, 2), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b565) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 59), (2, 65), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b567) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 59), (2, 67), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b56c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(1, 69), (2, 67), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b56e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 69), (2, 71), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b572) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 69), (2, 73), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b576) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(1, 69), (2, 73), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b57b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(1, 69), (2, 73), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b584) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 77), (2, 73), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b589) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 79), (2, 73), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b58d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(1, 81), (2, 73), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b590) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(1, 81), (2, 73), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b595) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(1, 81), (2, 73), (4, 4), (6, 6), (7, 61), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b59e) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11b53b_1 code

theorem block_l11b53b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11b53b :=
  Rest.liftedBlock (rest_l11b53b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11b53b x hx)

theorem rest_l11b5a3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11b5a3 bytes_l11b5a3) (entryMap (live .l11b5a3))
      3 0x11b5a3 bytes_l11b5a3 b_l11b5a3 := by
  have f0 : InstrSpec 0x11b5a3 [0x48, 0xC7, 0x44, 0x24, 0x30, 0xFE, 0xFF, 0xFF, 0xFF] (StorePre 0x11b5a3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11b5a3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b5a3 (.sib 4 none 0 (.d8 0x30)) 0xfffffffe)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11b5a3 (.sib 4 none 0 (.d8 0x30)) 0xfffffffe).toInstrSpec (mov_m64_imm32_effect_step 0x11b5a3 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0xfffffffe) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11b5ac [0x48, 0xC7, 0x44, 0x24, 0x18, 0xFF, 0xFF, 0xFF, 0xFF] (StorePre 0x11b5ac 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b5ac + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b5ac (.sib 4 none 0 (.d8 0x18)) 0xffffffff)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11b5ac (.sib 4 none 0 (.d8 0x18)) 0xffffffff).toInstrSpec (mov_m64_imm32_effect_step 0x11b5ac 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0xffffffff) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11b5b5 [0x48, 0x89, 0x7C, 0x24, 0x28] (StorePre 0x11b5b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11b5b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b5b5 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b5b5 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x11b5b5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5ac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5b5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5ba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 56) (by decide) rfl

theorem block_l11b5a3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11b5a3 :=
  Rest.liftedBlock (rest_l11b5a3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11b5a3 x hx)

theorem rest_l11b5ba_9 [Bindings] (code : CodeMap) :
    Rest (n := 451) code lifted (codeRange 0x11b5ba bytes_l11b5ba) [(0, 356), (1, 378), (2, 447), (3, 362), (4, 4), (5, 445), (6, 432), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]
      16 0x11b82b bytes_l11b5ba_9 b_l11b5ba_9 := by
  have f180 : InstrSpec 0x11b82b [0x48, 0x29, 0xFA] (fun s => s.RIP = 0x11b82b) (subR64R64Effect 0x11b82b 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11b82b 2 7).toInstrSpec (sub_r64_r64_effect_step 0x11b82b 0x48 0xfa (by decide) (by decide)) pre_rip
  have f181 : InstrSpec 0x11b82e [0x48, 0xC1, 0xFD, 0x3F] (fun s => s.RIP = 0x11b82e) (sarR64Effect 0x11b82e 4 5 63)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (sarR64Effect_footprint 0x11b82e 4 5 63).toInstrSpec (sar_r64_imm8_effect_step 0x11b82e 0x48 0xfd 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f182 : InstrSpec 0x11b832 [0x48, 0x01, 0xD5] (fun s => s.RIP = 0x11b832) (addR64R64Effect 0x11b832 5 2)
      [.gpr 5, .gpr 2] [] [.reg 5, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b832 5 2).toInstrSpec (add_r64_r64_effect_step 0x11b832 0x48 0xd5 (by decide) (by decide)) pre_rip
  have f183 : InstrSpec 0x11b835 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x11b835) (movR64R64Effect 0x11b835 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11b835 2 3).toInstrSpec (mov_r64_r64_effect_step 0x11b835 0x48 0xda (by decide) (by decide)) pre_rip
  have f184 : InstrSpec 0x11b838 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x11b838) (notR64Effect 0x11b838 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x11b838 2).toInstrSpec (not_r64_effect_step 0x11b838 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f185 : InstrSpec 0x11b83b [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x11b83b) (movR64R64Effect 0x11b83b 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11b83b 6 7).toInstrSpec (mov_r64_r64_effect_step 0x11b83b 0x48 0xfe (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x11b83e [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x11b83e) (andR64R64Effect 0x11b83e 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11b83e 6 2).toInstrSpec (and_r64_r64_effect_step 0x11b83e 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f187 : InstrSpec 0x11b841 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x11b841) (orR64R64Effect 0x11b841 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11b841 2 7).toInstrSpec (or_r64_r64_effect_step 0x11b841 0x48 0xfa (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x11b844 [0x48, 0x21, 0xEA] (fun s => s.RIP = 0x11b844) (andR64R64Effect 0x11b844 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11b844 2 5).toInstrSpec (and_r64_r64_effect_step 0x11b844 0x48 0xea (by decide) (by decide)) pre_rip
  have f189 : InstrSpec 0x11b847 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x11b847) (orR64R64Effect 0x11b847 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11b847 2 6).toInstrSpec (or_r64_r64_effect_step 0x11b847 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f190 : InstrSpec 0x11b84a [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x11b84a) (shrR64Effect 0x11b84a 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x11b84a 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x11b84a 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f191 : InstrSpec 0x11b84e [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x11b84e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b84e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b84e 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b84e 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11b84e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f192 : InstrSpec 0x11b853 [0x45, 0x31, 0xED] (fun s => s.RIP = 0x11b853) (xorR32R32Effect 0x11b853 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b853 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b853 0x45 0xed (by decide) (by decide)) pre_rip
  have f193 : InstrSpec 0x11b856 [0x4C, 0x2B, 0x6C, 0x24, 0x08] (LoadPre 0x11b856 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b856 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b856 13 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11b856 13 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11b856 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f194 : InstrSpec 0x11b85b [0x41, 0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x11b85b) (movzxR32R8Effect 0x11b85b 4 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x11b85b 4 7 8).toInstrSpec (movzx_r32_r8_rex_effect_step 0x11b85b 0x41 (by decide) 0xf8 (by decide)) pre_rip
  have f195 : InstrSpec 0x11b85f [0xE8, 0xEC, 0xC4, 0x00, 0x00] (PushPre 0x11b85f 5) (callEffect (fun _ => 0x127d50) 0x11b864)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11b85f 0x127d50 0x11b864).toInstrSpec (call_rel32_effect_step 0x11b85f 0xc4ec (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 451) (RestInside.out (n := 451) f180 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 452) (ρ' := [(0, 356), (1, 378), (2, 451), (3, 362), (4, 4), (5, 445), (6, 432), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b82e) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 453) (RestInside.out (n := 453) f181 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 454) (ρ' := [(0, 356), (1, 378), (2, 451), (3, 362), (4, 4), (5, 453), (6, 432), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b832) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 455) (RestInside.out (n := 455) f182 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 456) (ρ' := [(0, 356), (1, 378), (2, 451), (3, 362), (4, 4), (5, 455), (6, 432), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b835) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 457) (RestInside.out (n := 457) f183 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 458) (ρ' := [(0, 356), (1, 378), (2, 457), (3, 362), (4, 4), (5, 455), (6, 432), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b838) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 459) (RestInside.out (n := 459) f184 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 460) (ρ' := [(0, 356), (1, 378), (2, 459), (3, 362), (4, 4), (5, 455), (6, 432), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b83b) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 461) (RestInside.out (n := 461) f185 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 462) (ρ' := [(0, 356), (1, 378), (2, 459), (3, 362), (4, 4), (5, 455), (6, 461), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b83e) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 463) (RestInside.out (n := 463) f186 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 464) (ρ' := [(0, 356), (1, 378), (2, 459), (3, 362), (4, 4), (5, 455), (6, 463), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b841) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 465) (RestInside.out (n := 465) f187 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 466) (ρ' := [(0, 356), (1, 378), (2, 465), (3, 362), (4, 4), (5, 455), (6, 463), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b844) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 467) (RestInside.out (n := 467) f188 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 468) (ρ' := [(0, 356), (1, 378), (2, 467), (3, 362), (4, 4), (5, 455), (6, 463), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b847) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 469) (RestInside.out (n := 469) f189 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 470) (ρ' := [(0, 356), (1, 378), (2, 469), (3, 362), (4, 4), (5, 455), (6, 463), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b84a) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 471) (RestInside.out (n := 471) f190 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 472) (ρ' := [(0, 356), (1, 378), (2, 471), (3, 362), (4, 4), (5, 455), (6, 463), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b84e) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 473) (RestInside.exec (n := 473) (ρ' := [(0, 356), (1, 378), (2, 471), (3, 362), (4, 4), (5, 455), (6, 463), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b853) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 474) (RestInside.out (n := 474) f192 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 475) (ρ' := [(0, 356), (1, 378), (2, 471), (3, 362), (4, 4), (5, 455), (6, 463), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 474), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b856) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 476) (RestInside.out (n := 476) f193 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 477) (ρ' := [(0, 356), (1, 378), (2, 471), (3, 362), (4, 4), (5, 455), (6, 463), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 476), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b85b) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 478) (RestInside.out (n := 478) f194 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 479) (ρ' := [(0, 356), (1, 378), (2, 471), (3, 362), (4, 4), (5, 455), (6, 463), (7, 478), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 476), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b85f) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 480) (RestInside.out (n := 480) f195 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 481) (ρ' := [(0, 356), (1, 378), (2, 471), (3, 362), (4, 480), (5, 455), (6, 463), (7, 478), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 476), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f195 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 482) (by decide) (by decide) rfl rfl

theorem rest_l11b5ba_8 [Bindings] (code : CodeMap) :
    Rest (n := 412) code lifted (codeRange 0x11b5ba bytes_l11b5ba) [(0, 356), (1, 378), (2, 409), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]
      36 0x11b7e4 bytes_l11b5ba_8 b_l11b5ba_8 := by
  have f160 : InstrSpec 0x11b7e4 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x11b7e4) (xorR32R32Effect 0x11b7e4 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b7e4 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b7e4 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x11b7e7 [0x4C, 0x2B, 0x74, 0x24, 0x08] (LoadPre 0x11b7e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b7e7 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b7e7 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 14, .gpr 4] [] [.reg 14, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11b7e7 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11b7e7 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f162 : InstrSpec 0x11b7ec [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x11b7ec) (movR64R64Effect 0x11b7ec 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11b7ec 2 15).toInstrSpec (mov_r64_r64_effect_step 0x11b7ec 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f163 : InstrSpec 0x11b7ef [0x48, 0x8B, 0x7C, 0x24, 0x30] (LoadPre 0x11b7ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11b7ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b7ef 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11b7ef 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x11b7ef 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f164 : InstrSpec 0x11b7f4 [0x48, 0x29, 0xFA] (fun s => s.RIP = 0x11b7f4) (subR64R64Effect 0x11b7f4 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11b7f4 2 7).toInstrSpec (sub_r64_r64_effect_step 0x11b7f4 0x48 0xfa (by decide) (by decide)) pre_rip
  have f165 : InstrSpec 0x11b7f7 [0x49, 0xC1, 0xFE, 0x3F] (fun s => s.RIP = 0x11b7f7) (sarR64Effect 0x11b7f7 4 14 63)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (sarR64Effect_footprint 0x11b7f7 4 14 63).toInstrSpec (sar_r64_imm8_effect_step 0x11b7f7 0x49 0xfe 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f166 : InstrSpec 0x11b7fb [0x49, 0x01, 0xD6] (fun s => s.RIP = 0x11b7fb) (addR64R64Effect 0x11b7fb 14 2)
      [.gpr 14, .gpr 2] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b7fb 14 2).toInstrSpec (add_r64_r64_effect_step 0x11b7fb 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f167 : InstrSpec 0x11b7fe [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x11b7fe) (movR64R64Effect 0x11b7fe 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11b7fe 2 15).toInstrSpec (mov_r64_r64_effect_step 0x11b7fe 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x11b801 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x11b801) (notR64Effect 0x11b801 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x11b801 2).toInstrSpec (not_r64_effect_step 0x11b801 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f169 : InstrSpec 0x11b804 [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x11b804) (movR64R64Effect 0x11b804 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11b804 6 7).toInstrSpec (mov_r64_r64_effect_step 0x11b804 0x48 0xfe (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x11b807 [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x11b807) (andR64R64Effect 0x11b807 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11b807 6 2).toInstrSpec (and_r64_r64_effect_step 0x11b807 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f171 : InstrSpec 0x11b80a [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x11b80a) (orR64R64Effect 0x11b80a 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11b80a 2 7).toInstrSpec (or_r64_r64_effect_step 0x11b80a 0x48 0xfa (by decide) (by decide)) pre_rip
  have f172 : InstrSpec 0x11b80d [0x4C, 0x21, 0xF2] (fun s => s.RIP = 0x11b80d) (andR64R64Effect 0x11b80d 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11b80d 2 14).toInstrSpec (and_r64_r64_effect_step 0x11b80d 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f173 : InstrSpec 0x11b810 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x11b810) (orR64R64Effect 0x11b810 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11b810 2 6).toInstrSpec (or_r64_r64_effect_step 0x11b810 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f174 : InstrSpec 0x11b813 [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x11b813) (shrR64Effect 0x11b813 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x11b813 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x11b813 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x11b817 [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x11b817 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b817 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b817 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b817 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11b817 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f176 : InstrSpec 0x11b81c [0x31, 0xED] (fun s => s.RIP = 0x11b81c) (xorR32R32Effect 0x11b81c 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b81c 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x11b81c 0xed (by decide)) pre_rip
  have f177 : InstrSpec 0x11b81e [0x48, 0x2B, 0x6C, 0x24, 0x08] (LoadPre 0x11b81e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b81e + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b81e 5 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 5, .gpr 4] [] [.reg 5, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11b81e 5 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11b81e 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f178 : InstrSpec 0x11b823 [0x48, 0x89, 0xDA] (fun s => s.RIP = 0x11b823) (movR64R64Effect 0x11b823 2 3)
      [.gpr 3] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11b823 2 3).toInstrSpec (mov_r64_r64_effect_step 0x11b823 0x48 0xda (by decide) (by decide)) pre_rip
  have f179 : InstrSpec 0x11b826 [0x48, 0x8B, 0x7C, 0x24, 0x18] (LoadPre 0x11b826 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b826 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b826 7 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11b826 7 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11b826 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 412) (RestInside.out (n := 412) f160 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 413) (ρ' := [(0, 356), (1, 378), (2, 409), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 412), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7e7) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 414) (RestInside.out (n := 414) f161 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 415) (ρ' := [(0, 356), (1, 378), (2, 409), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 414), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7ec) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 416) (RestInside.out (n := 416) f162 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 417) (ρ' := [(0, 356), (1, 378), (2, 416), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 414), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7ef) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 418) (RestInside.out (n := 418) f163 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 419) (ρ' := [(0, 356), (1, 378), (2, 416), (3, 362), (4, 4), (5, 236), (6, 401), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 414), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7f4) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 420) (RestInside.out (n := 420) f164 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 421) (ρ' := [(0, 356), (1, 378), (2, 420), (3, 362), (4, 4), (5, 236), (6, 401), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 414), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7f7) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 422) (RestInside.out (n := 422) f165 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 423) (ρ' := [(0, 356), (1, 378), (2, 420), (3, 362), (4, 4), (5, 236), (6, 401), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 422), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7fb) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 424) (RestInside.out (n := 424) f166 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 425) (ρ' := [(0, 356), (1, 378), (2, 420), (3, 362), (4, 4), (5, 236), (6, 401), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7fe) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 426) (RestInside.out (n := 426) f167 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 427) (ρ' := [(0, 356), (1, 378), (2, 426), (3, 362), (4, 4), (5, 236), (6, 401), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b801) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 428) (RestInside.out (n := 428) f168 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 429) (ρ' := [(0, 356), (1, 378), (2, 428), (3, 362), (4, 4), (5, 236), (6, 401), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b804) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 430) (RestInside.out (n := 430) f169 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 431) (ρ' := [(0, 356), (1, 378), (2, 428), (3, 362), (4, 4), (5, 236), (6, 430), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b807) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 432) (RestInside.out (n := 432) f170 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 433) (ρ' := [(0, 356), (1, 378), (2, 428), (3, 362), (4, 4), (5, 236), (6, 432), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b80a) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 434) (RestInside.out (n := 434) f171 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 435) (ρ' := [(0, 356), (1, 378), (2, 434), (3, 362), (4, 4), (5, 236), (6, 432), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b80d) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 436) (RestInside.out (n := 436) f172 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 437) (ρ' := [(0, 356), (1, 378), (2, 436), (3, 362), (4, 4), (5, 236), (6, 432), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b810) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 438) (RestInside.out (n := 438) f173 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 439) (ρ' := [(0, 356), (1, 378), (2, 438), (3, 362), (4, 4), (5, 236), (6, 432), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b813) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 440) (RestInside.out (n := 440) f174 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 441) (ρ' := [(0, 356), (1, 378), (2, 440), (3, 362), (4, 4), (5, 236), (6, 432), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b817) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 442) (RestInside.exec (n := 442) (ρ' := [(0, 356), (1, 378), (2, 440), (3, 362), (4, 4), (5, 236), (6, 432), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b81c) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 443) (RestInside.out (n := 443) f176 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 444) (ρ' := [(0, 356), (1, 378), (2, 440), (3, 362), (4, 4), (5, 443), (6, 432), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b81e) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 445) (RestInside.out (n := 445) f177 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 446) (ρ' := [(0, 356), (1, 378), (2, 440), (3, 362), (4, 4), (5, 445), (6, 432), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b823) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 447) (RestInside.out (n := 447) f178 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 448) (ρ' := [(0, 356), (1, 378), (2, 447), (3, 362), (4, 4), (5, 445), (6, 432), (7, 418), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b826) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 449) (RestInside.out (n := 449) f179 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 450) (ρ' := [(0, 356), (1, 378), (2, 447), (3, 362), (4, 4), (5, 445), (6, 432), (7, 449), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b82b) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b5ba_9 code

theorem rest_l11b5ba_7 [Bindings] (code : CodeMap) :
    Rest (n := 375) code lifted (codeRange 0x11b5ba bytes_l11b5ba) [(0, 356), (1, 332), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 373), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]
      56 0x11b799 bytes_l11b5ba_7 b_l11b5ba_7 := by
  have f140 : InstrSpec 0x11b799 [0x48, 0xC1, 0xEF, 0x3F] (fun s => s.RIP = 0x11b799) (shrR64Effect 0x11b799 4 7 63)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x11b799 4 7 63).toInstrSpec (shr_r64_imm8_effect_step 0x11b799 0x48 0xef 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f141 : InstrSpec 0x11b79d [0x48, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x11b79d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b79d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b79d 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b79d 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11b79d 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f142 : InstrSpec 0x11b7a2 [0x48, 0x8D, 0x4C, 0x24, 0x08] (fun s => s.RIP = 0x11b7a2) (leaR64Effect 0x11b7a2 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x11b7a2 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x11b7a2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f143 : InstrSpec 0x11b7a7 [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x11b7a7) (xorR32R32Effect 0x11b7a7 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b7a7 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b7a7 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x11b7aa [0x4C, 0x2B, 0x64, 0x24, 0x08] (LoadPre 0x11b7aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b7aa + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b7aa 12 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 12, .gpr 4] [] [.reg 12, .flags, .rip] :=
    (subR64M64Effect_footprint 0x11b7aa 12 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (sub_r64_m64_effect_step 0x11b7aa 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f145 : InstrSpec 0x11b7af [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x11b7af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11b7af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b7af 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b7af 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x11b7af 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f146 : InstrSpec 0x11b7b4 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x11b7b4) (movR64R64Effect 0x11b7b4 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11b7b4 2 0).toInstrSpec (mov_r64_r64_effect_step 0x11b7b4 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f147 : InstrSpec 0x11b7b7 [0x48, 0x8B, 0x7C, 0x24, 0x28] (LoadPre 0x11b7b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11b7b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b7b7 7 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11b7b7 7 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x11b7b7 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f148 : InstrSpec 0x11b7bc [0x48, 0x29, 0xFA] (fun s => s.RIP = 0x11b7bc) (subR64R64Effect 0x11b7bc 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (subR64R64Effect_footprint 0x11b7bc 2 7).toInstrSpec (sub_r64_r64_effect_step 0x11b7bc 0x48 0xfa (by decide) (by decide)) pre_rip
  have f149 : InstrSpec 0x11b7bf [0x49, 0xC1, 0xFC, 0x3F] (fun s => s.RIP = 0x11b7bf) (sarR64Effect 0x11b7bf 4 12 63)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (sarR64Effect_footprint 0x11b7bf 4 12 63).toInstrSpec (sar_r64_imm8_effect_step 0x11b7bf 0x49 0xfc 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x11b7c3 [0x49, 0x01, 0xD4] (fun s => s.RIP = 0x11b7c3) (addR64R64Effect 0x11b7c3 12 2)
      [.gpr 12, .gpr 2] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b7c3 12 2).toInstrSpec (add_r64_r64_effect_step 0x11b7c3 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x11b7c6 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x11b7c6) (movR64R64Effect 0x11b7c6 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x11b7c6 2 0).toInstrSpec (mov_r64_r64_effect_step 0x11b7c6 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x11b7c9 [0x48, 0xF7, 0xD2] (fun s => s.RIP = 0x11b7c9) (notR64Effect 0x11b7c9 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR64Effect_footprint 0x11b7c9 2).toInstrSpec (not_r64_effect_step 0x11b7c9 0x48 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f153 : InstrSpec 0x11b7cc [0x48, 0x89, 0xFE] (fun s => s.RIP = 0x11b7cc) (movR64R64Effect 0x11b7cc 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11b7cc 6 7).toInstrSpec (mov_r64_r64_effect_step 0x11b7cc 0x48 0xfe (by decide) (by decide)) pre_rip
  have f154 : InstrSpec 0x11b7cf [0x48, 0x21, 0xD6] (fun s => s.RIP = 0x11b7cf) (andR64R64Effect 0x11b7cf 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11b7cf 6 2).toInstrSpec (and_r64_r64_effect_step 0x11b7cf 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f155 : InstrSpec 0x11b7d2 [0x48, 0x09, 0xFA] (fun s => s.RIP = 0x11b7d2) (orR64R64Effect 0x11b7d2 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11b7d2 2 7).toInstrSpec (or_r64_r64_effect_step 0x11b7d2 0x48 0xfa (by decide) (by decide)) pre_rip
  have f156 : InstrSpec 0x11b7d5 [0x4C, 0x21, 0xE2] (fun s => s.RIP = 0x11b7d5) (andR64R64Effect 0x11b7d5 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11b7d5 2 12).toInstrSpec (and_r64_r64_effect_step 0x11b7d5 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x11b7d8 [0x48, 0x09, 0xF2] (fun s => s.RIP = 0x11b7d8) (orR64R64Effect 0x11b7d8 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11b7d8 2 6).toInstrSpec (or_r64_r64_effect_step 0x11b7d8 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f158 : InstrSpec 0x11b7db [0x48, 0xC1, 0xEA, 0x3F] (fun s => s.RIP = 0x11b7db) (shrR64Effect 0x11b7db 4 2 63)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x11b7db 4 2 63).toInstrSpec (shr_r64_imm8_effect_step 0x11b7db 0x48 0xea 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x11b7df [0x48, 0x89, 0x54, 0x24, 0x08] (StorePre 0x11b7df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b7df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b7df 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b7df 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11b7df 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 375) (RestInside.out (n := 375) f140 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 376) (ρ' := [(0, 356), (1, 332), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 375), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b79d) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 377) (RestInside.exec (n := 377) (ρ' := [(0, 356), (1, 332), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 375), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7a2) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f142 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 356), (1, 378), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 375), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7a7) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f143 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 356), (1, 378), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 375), (8, 365), (9, 275), (10, 327), (11, 261), (12, 380), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7aa) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f144 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 356), (1, 378), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 375), (8, 365), (9, 275), (10, 327), (11, 261), (12, 382), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7af) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 384) (RestInside.exec (n := 384) (ρ' := [(0, 356), (1, 378), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 375), (8, 365), (9, 275), (10, 327), (11, 261), (12, 382), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7b4) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 385) (RestInside.out (n := 385) f146 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 386) (ρ' := [(0, 356), (1, 378), (2, 385), (3, 362), (4, 4), (5, 236), (6, 320), (7, 375), (8, 365), (9, 275), (10, 327), (11, 261), (12, 382), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7b7) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 387) (RestInside.out (n := 387) f147 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 388) (ρ' := [(0, 356), (1, 378), (2, 385), (3, 362), (4, 4), (5, 236), (6, 320), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 382), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7bc) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f148 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 356), (1, 378), (2, 389), (3, 362), (4, 4), (5, 236), (6, 320), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 382), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7bf) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f149 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 392) (ρ' := [(0, 356), (1, 378), (2, 389), (3, 362), (4, 4), (5, 236), (6, 320), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 391), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7c3) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 393) (RestInside.out (n := 393) f150 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 394) (ρ' := [(0, 356), (1, 378), (2, 389), (3, 362), (4, 4), (5, 236), (6, 320), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7c6) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 395) (RestInside.out (n := 395) f151 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 396) (ρ' := [(0, 356), (1, 378), (2, 395), (3, 362), (4, 4), (5, 236), (6, 320), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7c9) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 397) (RestInside.out (n := 397) f152 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 398) (ρ' := [(0, 356), (1, 378), (2, 397), (3, 362), (4, 4), (5, 236), (6, 320), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7cc) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 399) (RestInside.out (n := 399) f153 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 400) (ρ' := [(0, 356), (1, 378), (2, 397), (3, 362), (4, 4), (5, 236), (6, 399), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7cf) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 401) (RestInside.out (n := 401) f154 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 402) (ρ' := [(0, 356), (1, 378), (2, 397), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7d2) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.out (n := 403) f155 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 404) (ρ' := [(0, 356), (1, 378), (2, 403), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7d5) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 405) (RestInside.out (n := 405) f156 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 406) (ρ' := [(0, 356), (1, 378), (2, 405), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7d8) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 407) (RestInside.out (n := 407) f157 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 408) (ρ' := [(0, 356), (1, 378), (2, 407), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7db) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 409) (RestInside.out (n := 409) f158 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 410) (ρ' := [(0, 356), (1, 378), (2, 409), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7df) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 411) (RestInside.exec (n := 411) (ρ' := [(0, 356), (1, 378), (2, 409), (3, 362), (4, 4), (5, 236), (6, 401), (7, 387), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b7e4) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11b5ba_8 code

theorem rest_l11b5ba_6 [Bindings] (code : CodeMap) :
    Rest (n := 329) code lifted (codeRange 0x11b5ba bytes_l11b5ba) [(0, 325), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 320), (7, 140), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]
      76 0x11b755 bytes_l11b5ba_6 b_l11b5ba_6 := by
  have f120 : InstrSpec 0x11b755 [0x49, 0xF7, 0xE2] (fun s => s.RIP = 0x11b755) (mulR64Effect 0x11b755 10)
      [.gpr 10, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b755 10).toInstrSpec (mul_r64_effect_step 0x11b755 0x49 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x11b758 [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x11b758) (movR64R64Effect 0x11b758 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11b758 1 2).toInstrSpec (mov_r64_r64_effect_step 0x11b758 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x11b75b [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11b75b) (movR64R64Effect 0x11b75b 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11b75b 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11b75b 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x11b75e [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x11b75e) (movR64R64Effect 0x11b75e 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b75e 0 15).toInstrSpec (mov_r64_r64_effect_step 0x11b75e 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x11b761 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x11b761) (mulR64Effect 0x11b761 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b761 9).toInstrSpec (mul_r64_effect_step 0x11b761 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x11b764 [0x4C, 0x01, 0xD8] (fun s => s.RIP = 0x11b764) (addR64R64Effect 0x11b764 0 11)
      [.gpr 0, .gpr 11] [] [.reg 0, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b764 0 11).toInstrSpec (add_r64_r64_effect_step 0x11b764 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f126 : InstrSpec 0x11b767 [0x48, 0x83, 0xD2, 0x00] (fun s => s.RIP = 0x11b767) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b767 2 0x0))
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x11b767 2 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x11b767 0x48 0xd2 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f127 : InstrSpec 0x11b76b [0x31, 0xDB] (fun s => s.RIP = 0x11b76b) (xorR32R32Effect 0x11b76b 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b76b 2 3 3).toInstrSpec (xor_r32_r32_effect_step 0x11b76b 0xdb (by decide)) pre_rip
  have f128 : InstrSpec 0x11b76d [0x4D, 0x01, 0xC7] (fun s => s.RIP = 0x11b76d) (addR64R64Effect 0x11b76d 15 8)
      [.gpr 15, .gpr 8] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b76d 15 8).toInstrSpec (add_r64_r64_effect_step 0x11b76d 0x4d 0xc7 (by decide) (by decide)) pre_rip
  have f129 : InstrSpec 0x11b770 [0x0F, 0x92, 0xC3] (fun s => s.RIP = 0x11b770) (atFlags (condHolds 2) (setccR8Effect 0x11b770 3 3))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .rip] :=
    (setccR8Effect_footprint 0x11b770 3 3 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x11b770 2 0xc3 (by decide) (by decide) c)) pre_rip
  have f130 : InstrSpec 0x11b773 [0x48, 0x03, 0x7C, 0x24, 0x10] (LoadPre 0x11b773 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b773 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11b773 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (addR64M64Effect_footprint 0x11b773 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (add_r64_m64_effect_step 0x11b773 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f131 : InstrSpec 0x11b778 [0x48, 0x11, 0xC8] (fun s => s.RIP = 0x11b778) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b778 0 1))
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b778 0 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b778 0x48 0xc8 c (by decide) (by decide))) pre_rip
  have f132 : InstrSpec 0x11b77b [0x49, 0x11, 0xD7] (fun s => s.RIP = 0x11b77b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b77b 15 2))
      [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b77b 15 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b77b 0x49 0xd7 c (by decide) (by decide))) pre_rip
  have f133 : InstrSpec 0x11b77e [0x48, 0x11, 0xF3] (fun s => s.RIP = 0x11b77e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b77e 3 6))
      [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b77e 3 6).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b77e 0x48 0xf3 c (by decide) (by decide))) pre_rip
  have f134 : InstrSpec 0x11b781 [0x41, 0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x11b781) (atFlags (condHolds 2) (setccR8Effect 0x11b781 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x11b781 4 8 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b781 2 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f135 : InstrSpec 0x11b785 [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x11b785 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b785 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b785 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b785 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11b785 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f136 : InstrSpec 0x11b78a [0x49, 0x8D, 0x14, 0x3A] (fun s => s.RIP = 0x11b78a) (leaR64Effect 0x11b78a 2 (.sib 10 (some 7) 0 .none))
      [.gpr 10, .gpr 7] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11b78a 2 (.sib 10 (some 7) 0 .none)).toInstrSpec (lea_r64_effect_step 0x11b78a 0x49 (by decide) 2 (.sib 10 (some 7) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x11b78e [0x48, 0x89, 0x54, 0x24, 0x20] (StorePre 0x11b78e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b78e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b78e 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b78e 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x11b78e 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f138 : InstrSpec 0x11b793 [0x48, 0xF7, 0xD7] (fun s => s.RIP = 0x11b793) (notR64Effect 0x11b793 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (notR64Effect_footprint 0x11b793 7).toInstrSpec (not_r64_effect_step 0x11b793 0x48 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f139 : InstrSpec 0x11b796 [0x48, 0x09, 0xD7] (fun s => s.RIP = 0x11b796) (orR64R64Effect 0x11b796 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (orR64R64Effect_footprint 0x11b796 7 2).toInstrSpec (or_r64_r64_effect_step 0x11b796 0x48 0xd7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 329) (RestInside.out (n := 329) f120 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 330) f120 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 331) (ρ' := [(0, 329), (1, 299), (2, 330), (3, 100), (4, 4), (5, 236), (6, 320), (7, 140), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b758) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f121 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 329), (1, 332), (2, 330), (3, 100), (4, 4), (5, 236), (6, 320), (7, 140), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b75b) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f122 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 335) (ρ' := [(0, 329), (1, 332), (2, 330), (3, 100), (4, 4), (5, 236), (6, 320), (7, 334), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b75e) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f123 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 336), (1, 332), (2, 330), (3, 100), (4, 4), (5, 236), (6, 320), (7, 334), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b761) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f124 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 339) f124 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 340) (ρ' := [(0, 338), (1, 332), (2, 339), (3, 100), (4, 4), (5, 236), (6, 320), (7, 334), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b764) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 341) (RestInside.out (n := 341) f125 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 342) f125 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 343) (ρ' := [(0, 341), (1, 332), (2, 339), (3, 100), (4, 4), (5, 236), (6, 320), (7, 334), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (16, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b767) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f126 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 341), (1, 332), (2, 344), (3, 100), (4, 4), (5, 236), (6, 320), (7, 334), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b76b) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.out (n := 346) f127 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 347) (ρ' := [(0, 341), (1, 332), (2, 344), (3, 346), (4, 4), (5, 236), (6, 320), (7, 334), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b76d) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f128 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 349) f128 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 350) (ρ' := [(0, 341), (1, 332), (2, 344), (3, 346), (4, 4), (5, 236), (6, 320), (7, 334), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 348), (16, 349), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b770) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f129 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 341), (1, 332), (2, 344), (3, 351), (4, 4), (5, 236), (6, 320), (7, 334), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 348), (16, 349), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b773) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f130 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 354) f130 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 355) (ρ' := [(0, 341), (1, 332), (2, 344), (3, 351), (4, 4), (5, 236), (6, 320), (7, 353), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 348), (16, 354), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b778) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 356) (RestInside.out (n := 356) f131 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 357) f131 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11b778 0 1 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 358) (ρ' := [(0, 356), (1, 332), (2, 344), (3, 351), (4, 4), (5, 236), (6, 320), (7, 353), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 348), (16, 357), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b77b) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f132 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 360) f132 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11b77b 15 2 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 361) (ρ' := [(0, 356), (1, 332), (2, 344), (3, 351), (4, 4), (5, 236), (6, 320), (7, 353), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (16, 360), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b77e) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 362) (RestInside.out (n := 362) f133 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 363) f133 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11b77e 3 6 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 364) (ρ' := [(0, 356), (1, 332), (2, 344), (3, 362), (4, 4), (5, 236), (6, 320), (7, 353), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (16, 363), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b781) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f134 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 356), (1, 332), (2, 344), (3, 362), (4, 4), (5, 236), (6, 320), (7, 353), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (16, 363), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b785) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.exec (n := 367) (ρ' := [(0, 356), (1, 332), (2, 344), (3, 362), (4, 4), (5, 236), (6, 320), (7, 353), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (16, 363), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b78a) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 368) (RestInside.out (n := 368) f136 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 369) (ρ' := [(0, 356), (1, 332), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 353), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (16, 363), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b78e) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 370) (RestInside.exec (n := 370) (ρ' := [(0, 356), (1, 332), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 353), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (16, 363), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b793) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 371) (RestInside.out (n := 371) f138 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 372) (ρ' := [(0, 356), (1, 332), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 371), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (16, 363), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b796) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 373) (RestInside.out (n := 373) f139 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 374) (ρ' := [(0, 356), (1, 332), (2, 368), (3, 362), (4, 4), (5, 236), (6, 320), (7, 373), (8, 365), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b799) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b5ba_7 code

theorem rest_l11b5ba_5 [Bindings] (code : CodeMap) :
    Rest (n := 283) code lifted (codeRange 0x11b5ba bytes_l11b5ba) [(0, 277), (1, 271), (2, 278), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 280), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 281), (22, 22), (39, 39), (50, 50), (51, 51)]
      96 0x11b714 bytes_l11b5ba_5 b_l11b5ba_5 := by
  have f100 : InstrSpec 0x11b714 [0x48, 0x11, 0xCA] (fun s => s.RIP = 0x11b714) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b714 2 1))
      [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b714 2 1).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b714 0x48 0xca c (by decide) (by decide))) pre_rip
  have f101 : InstrSpec 0x11b717 [0x31, 0xC9] (fun s => s.RIP = 0x11b717) (xorR32R32Effect 0x11b717 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b717 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x11b717 0xc9 (by decide)) pre_rip
  have f102 : InstrSpec 0x11b719 [0x49, 0x01, 0xC0] (fun s => s.RIP = 0x11b719) (addR64R64Effect 0x11b719 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b719 8 0).toInstrSpec (add_r64_r64_effect_step 0x11b719 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x11b71c [0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x11b71c) (atFlags (condHolds 2) (setccR8Effect 0x11b71c 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x11b71c 3 1 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x11b71c 2 0xc1 (by decide) (by decide) c)) pre_rip
  have f104 : InstrSpec 0x11b71f [0x4D, 0x01, 0xF8] (fun s => s.RIP = 0x11b71f) (addR64R64Effect 0x11b71f 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b71f 8 15).toInstrSpec (add_r64_r64_effect_step 0x11b71f 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x11b722 [0x48, 0x11, 0xD1] (fun s => s.RIP = 0x11b722) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b722 1 2))
      [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b722 1 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b722 0x48 0xd1 c (by decide) (by decide))) pre_rip
  have f106 : InstrSpec 0x11b725 [0x31, 0xC0] (fun s => s.RIP = 0x11b725) (xorR32R32Effect 0x11b725 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b725 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x11b725 0xc0 (by decide)) pre_rip
  have f107 : InstrSpec 0x11b727 [0x48, 0x01, 0xF1] (fun s => s.RIP = 0x11b727) (addR64R64Effect 0x11b727 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b727 1 6).toInstrSpec (add_r64_r64_effect_step 0x11b727 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x11b72a [0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x11b72a) (atFlags (condHolds 2) (setccR8Effect 0x11b72a 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x11b72a 3 0 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x11b72a 2 0xc0 (by decide) (by decide) c)) pre_rip
  have f109 : InstrSpec 0x11b72d [0x49, 0x01, 0xFE] (fun s => s.RIP = 0x11b72d) (addR64R64Effect 0x11b72d 14 7)
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b72d 14 7).toInstrSpec (add_r64_r64_effect_step 0x11b72d 0x49 0xfe (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x11b730 [0xBE, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11b730) (movR32Imm32Effect 0x11b730 5 6 0x0)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x11b730 5 6 0x0).toInstrSpec (mov_r32_imm32_effect_step 0x11b730 0xbe (by decide) 0x0) pre_rip
  have f111 : InstrSpec 0x11b735 [0x49, 0x0F, 0x42, 0xF1] (fun s => s.RIP = 0x11b735) (atFlags (condHolds 2) (cmovR64R64Effect 0x11b735 4 6 9))
      [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 6, .rip] :=
    (cmovR64R64Effect_footprint 0x11b735 4 6 9 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11b735 2 0x49 (by decide) 0xf1 (by decide) c)) pre_rip
  have f112 : InstrSpec 0x11b739 [0x48, 0x83, 0xD0, 0x00] (fun s => s.RIP = 0x11b739) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b739 0 0x0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 0, .flags, .rip] :=
    (adcR64Imm8Effect_footprint 0x11b739 0 0x0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_imm8_effect_step 0x11b739 0x48 0xd0 0x0 c (by decide) (by decide) (by decide))) pre_rip
  have f113 : InstrSpec 0x11b73d [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x11b73d) (xorR32R32Effect 0x11b73d 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b73d 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b73d 0x45 0xff (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x11b740 [0x48, 0x01, 0xCE] (fun s => s.RIP = 0x11b740) (addR64R64Effect 0x11b740 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b740 6 1).toInstrSpec (add_r64_r64_effect_step 0x11b740 0x48 0xce (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x11b743 [0x41, 0x0F, 0x92, 0xC7] (fun s => s.RIP = 0x11b743) (atFlags (condHolds 2) (setccR8Effect 0x11b743 4 15))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .rip] :=
    (setccR8Effect_footprint 0x11b743 4 15 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b743 2 0x41 (by decide) 0xc7 (by decide) c)) pre_rip
  have f116 : InstrSpec 0x11b747 [0x4C, 0x01, 0xF6] (fun s => s.RIP = 0x11b747) (addR64R64Effect 0x11b747 6 14)
      [.gpr 6, .gpr 14] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b747 6 14).toInstrSpec (add_r64_r64_effect_step 0x11b747 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x11b74a [0x49, 0x11, 0xC7] (fun s => s.RIP = 0x11b74a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b74a 15 0))
      [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b74a 15 0).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b74a 0x49 0xc7 c (by decide) (by decide))) pre_rip
  have f118 : InstrSpec 0x11b74d [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x11b74d) (movR64R64Effect 0x11b74d 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b74d 0 15).toInstrSpec (mov_r64_r64_effect_step 0x11b74d 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x11b750 [0x4C, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x11b750 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b750 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b750 10 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x11b750 10 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11b750 0x4c (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f100 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 277), (1, 271), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 280), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b717) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f101 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 277), (1, 285), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 280), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b719) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f102 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 288) f102 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 289) (ρ' := [(0, 277), (1, 285), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 287), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 288), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b71c) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f103 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 277), (1, 290), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 287), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 288), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b71f) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f104 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 293) f104 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 294) (ρ' := [(0, 277), (1, 290), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 293), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b722) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f105 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 277), (1, 295), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b725) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.out (n := 297) f106 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 298) (ρ' := [(0, 297), (1, 295), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b727) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 299) (RestInside.out (n := 299) f107 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 300) f107 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 301) (ρ' := [(0, 297), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 300), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b72a) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f108 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 302), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 300), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b72d) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f109 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 305) f109 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 306) (ρ' := [(0, 302), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 203), (16, 305), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b730) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f110 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 308) (ρ' := [(0, 302), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 307), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 203), (16, 305), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b735) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f111 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 302), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 309), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 203), (16, 305), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b739) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f112 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 311), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 309), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b73d) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f113 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 314) (ρ' := [(0, 311), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 309), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 313), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b740) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 315) (RestInside.out (n := 315) f114 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 316) f114 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 317) (ρ' := [(0, 311), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 315), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 313), (16, 316), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b743) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f115 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 311), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 315), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 318), (16, 316), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b747) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f116 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 321) f116 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 322) (ρ' := [(0, 311), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 320), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 318), (16, 321), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b74a) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 323) (RestInside.out (n := 323) f117 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 324) (ρ' := [(0, 311), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 320), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b74d) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 325) (RestInside.out (n := 325) f118 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 326) (ρ' := [(0, 325), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 320), (7, 140), (8, 292), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b750) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 327) (RestInside.out (n := 327) f119 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 328) (ρ' := [(0, 325), (1, 299), (2, 283), (3, 100), (4, 4), (5, 236), (6, 320), (7, 140), (8, 292), (9, 275), (10, 327), (11, 261), (12, 222), (13, 234), (14, 304), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b755) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b5ba_6 code

theorem rest_l11b5ba_4 [Bindings] (code : CodeMap) :
    Rest (n := 236) code lifted (codeRange 0x11b5ba bytes_l11b5ba) [(0, 231), (1, 216), (2, 232), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]
      116 0x11b6c6 bytes_l11b5ba_4 b_l11b5ba_4 := by
  have f80 : InstrSpec 0x11b6c6 [0x48, 0x89, 0xC5] (fun s => s.RIP = 0x11b6c6) (movR64R64Effect 0x11b6c6 5 0)
      [.gpr 0] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x11b6c6 5 0).toInstrSpec (mov_r64_r64_effect_step 0x11b6c6 0x48 0xc5 (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x11b6c9 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x11b6c9) (movR64R64Effect 0x11b6c9 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b6c9 0 15).toInstrSpec (mov_r64_r64_effect_step 0x11b6c9 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x11b6cc [0x48, 0xBA, 0xC4, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x11b6cc) (movR64Imm64Effect 0x11b6cc 2 0x4551231950b75fc4)
      [] [] [.reg 2, .rip] :=
    (movR64Imm64Effect_footprint 0x11b6cc 2 0x4551231950b75fc4).toInstrSpec (mov_r64_imm64_effect_step 0x11b6cc 0x48 0xba (by decide) (by decide) 0x4551231950b75fc4) pre_rip
  have f83 : InstrSpec 0x11b6d6 [0x48, 0xF7, 0xE2] (fun s => s.RIP = 0x11b6d6) (mulR64Effect 0x11b6d6 2)
      [.gpr 2, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b6d6 2).toInstrSpec (mul_r64_effect_step 0x11b6d6 0x48 0xe2 (by decide) (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x11b6d9 [0x48, 0x03, 0x4C, 0x24, 0x10] (LoadPre 0x11b6d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b6d9 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11b6d9 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.reg 1, .flags, .rip] :=
    (addR64M64Effect_footprint 0x11b6d9 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (add_r64_m64_effect_step 0x11b6d9 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f85 : InstrSpec 0x11b6de [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x11b6de 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b6de + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b6de 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b6de 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11b6de 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f86 : InstrSpec 0x11b6e3 [0x49, 0x11, 0xDB] (fun s => s.RIP = 0x11b6e3) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6e3 11 3))
      [.gpr 11, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 11, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b6e3 11 3).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b6e3 0x49 0xdb c (by decide) (by decide))) pre_rip
  have f87 : InstrSpec 0x11b6e6 [0x4C, 0x11, 0xEA] (fun s => s.RIP = 0x11b6e6) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6e6 2 13))
      [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b6e6 2 13).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b6e6 0x4c 0xea c (by decide) (by decide))) pre_rip
  have f88 : InstrSpec 0x11b6e9 [0x45, 0x31, 0xC0] (fun s => s.RIP = 0x11b6e9) (xorR32R32Effect 0x11b6e9 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b6e9 3 8 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b6e9 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x11b6ec [0x49, 0x01, 0xEB] (fun s => s.RIP = 0x11b6ec) (addR64R64Effect 0x11b6ec 11 5)
      [.gpr 11, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b6ec 11 5).toInstrSpec (add_r64_r64_effect_step 0x11b6ec 0x49 0xeb (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x11b6ef [0x41, 0x0F, 0x92, 0xC0] (fun s => s.RIP = 0x11b6ef) (atFlags (condHolds 2) (setccR8Effect 0x11b6ef 4 8))
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .rip] :=
    (setccR8Effect_footprint 0x11b6ef 4 8 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b6ef 2 0x41 (by decide) 0xc0 (by decide) c)) pre_rip
  have f91 : InstrSpec 0x11b6f3 [0x49, 0x01, 0xC3] (fun s => s.RIP = 0x11b6f3) (addR64R64Effect 0x11b6f3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b6f3 11 0).toInstrSpec (add_r64_r64_effect_step 0x11b6f3 0x49 0xc3 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x11b6f6 [0x49, 0x11, 0xD0] (fun s => s.RIP = 0x11b6f6) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6f6 8 2))
      [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 8, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b6f6 8 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b6f6 0x49 0xd0 c (by decide) (by decide))) pre_rip
  have f93 : InstrSpec 0x11b6f9 [0x31, 0xC9] (fun s => s.RIP = 0x11b6f9) (xorR32R32Effect 0x11b6f9 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b6f9 2 1 1).toInstrSpec (xor_r32_r32_effect_step 0x11b6f9 0xc9 (by decide)) pre_rip
  have f94 : InstrSpec 0x11b6fb [0x4D, 0x01, 0xC8] (fun s => s.RIP = 0x11b6fb) (addR64R64Effect 0x11b6fb 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b6fb 8 9).toInstrSpec (add_r64_r64_effect_step 0x11b6fb 0x4d 0xc8 (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x11b6fe [0x0F, 0x92, 0xC1] (fun s => s.RIP = 0x11b6fe) (atFlags (condHolds 2) (setccR8Effect 0x11b6fe 3 1))
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 1, .rip] :=
    (setccR8Effect_footprint 0x11b6fe 3 1 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x11b6fe 2 0xc1 (by decide) (by decide) c)) pre_rip
  have f96 : InstrSpec 0x11b701 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x11b701) (movR64R64Effect 0x11b701 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b701 0 12).toInstrSpec (mov_r64_r64_effect_step 0x11b701 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x11b704 [0x49, 0xB9, 0xC4, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x11b704) (movR64Imm64Effect 0x11b704 9 0x4551231950b75fc4)
      [] [] [.reg 9, .rip] :=
    (movR64Imm64Effect_footprint 0x11b704 9 0x4551231950b75fc4).toInstrSpec (mov_r64_imm64_effect_step 0x11b704 0x49 0xb9 (by decide) (by decide) 0x4551231950b75fc4) pre_rip
  have f98 : InstrSpec 0x11b70e [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x11b70e) (mulR64Effect 0x11b70e 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b70e 9).toInstrSpec (mul_r64_effect_step 0x11b70e 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x11b711 [0x4D, 0x01, 0xD0] (fun s => s.RIP = 0x11b711) (addR64R64Effect 0x11b711 8 10)
      [.gpr 8, .gpr 10] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b711 8 10).toInstrSpec (add_r64_r64_effect_step 0x11b711 0x4d 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f80 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 231), (1, 216), (2, 232), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6c9) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f81 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 238), (1, 216), (2, 232), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6cc) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f82 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 238), (1, 216), (2, 240), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6d6) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f83 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 243) f83 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 244) (ρ' := [(0, 242), (1, 216), (2, 243), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6d9) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 246) f84 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 247) (ρ' := [(0, 242), (1, 245), (2, 243), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 234), (14, 206), (15, 203), (16, 246), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6de) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.exec (n := 248) (ρ' := [(0, 242), (1, 245), (2, 243), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 234), (14, 206), (15, 203), (16, 246), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6e3) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f86 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 250) f86 .CF (fun _ => rfl) (adcR64R64Effect_fresh 0x11b6e3 11 3 _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 251) (ρ' := [(0, 242), (1, 245), (2, 243), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 249), (12, 222), (13, 234), (14, 206), (15, 203), (16, 250), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6e6) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f87 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 242), (1, 245), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 249), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6e9) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.out (n := 254) f88 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 255) (ρ' := [(0, 242), (1, 245), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 254), (9, 144), (10, 227), (11, 249), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6ec) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f89 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 257) f89 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 258) (ρ' := [(0, 242), (1, 245), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 254), (9, 144), (10, 227), (11, 256), (12, 222), (13, 234), (14, 206), (15, 203), (16, 257), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6ef) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f90 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 242), (1, 245), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 259), (9, 144), (10, 227), (11, 256), (12, 222), (13, 234), (14, 206), (15, 203), (16, 257), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6f3) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f91 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 262) f91 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 263) (ρ' := [(0, 242), (1, 245), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 259), (9, 144), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 262), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6f6) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f92 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 242), (1, 245), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 264), (9, 144), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6f9) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.out (n := 266) f93 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 267) (ρ' := [(0, 242), (1, 266), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 264), (9, 144), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6fb) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f94 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 269) f94 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 270) (ρ' := [(0, 242), (1, 266), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 268), (9, 144), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 269), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6fe) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.out (n := 271) f95 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 272) (ρ' := [(0, 242), (1, 271), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 268), (9, 144), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 269), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b701) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f96 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 273), (1, 271), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 268), (9, 144), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 269), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b704) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f97 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 273), (1, 271), (2, 252), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 268), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 269), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b70e) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f98 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 278) f98 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 279) (ρ' := [(0, 277), (1, 271), (2, 278), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 268), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b711) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f99 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 281) f99 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 282) (ρ' := [(0, 277), (1, 271), (2, 278), (3, 100), (4, 4), (5, 236), (6, 184), (7, 140), (8, 280), (9, 275), (10, 227), (11, 261), (12, 222), (13, 234), (14, 206), (15, 203), (16, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b714) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b5ba_5 code

theorem rest_l11b5ba_3 [Bindings] (code : CodeMap) :
    Rest (n := 191) code lifted (codeRange 0x11b5ba bytes_l11b5ba) [(0, 189), (1, 84), (2, 175), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]
      136 0x11b683 bytes_l11b5ba_3 b_l11b5ba_3 := by
  have f60 : InstrSpec 0x11b683 [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x11b683) (mulR64Effect 0x11b683 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b683 13).toInstrSpec (mul_r64_effect_step 0x11b683 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x11b686 [0x49, 0x89, 0xC7] (fun s => s.RIP = 0x11b686) (movR64R64Effect 0x11b686 15 0)
      [.gpr 0] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x11b686 15 0).toInstrSpec (mov_r64_r64_effect_step 0x11b686 0x49 0xc7 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x11b689 [0x45, 0x31, 0xF6] (fun s => s.RIP = 0x11b689) (xorR32R32Effect 0x11b689 3 14 14)
      [.gpr 14, .gpr 14] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b689 3 14 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b689 0x45 0xf6 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x11b68c [0x4D, 0x01, 0xD7] (fun s => s.RIP = 0x11b68c) (addR64R64Effect 0x11b68c 15 10)
      [.gpr 15, .gpr 10] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b68c 15 10).toInstrSpec (add_r64_r64_effect_step 0x11b68c 0x4d 0xd7 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x11b68f [0x41, 0x0F, 0x92, 0xC6] (fun s => s.RIP = 0x11b68f) (atFlags (condHolds 2) (setccR8Effect 0x11b68f 4 14))
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .rip] :=
    (setccR8Effect_footprint 0x11b68f 4 14 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b68f 2 0x41 (by decide) 0xc6 (by decide) c)) pre_rip
  have f65 : InstrSpec 0x11b693 [0x4D, 0x01, 0xDF] (fun s => s.RIP = 0x11b693) (addR64R64Effect 0x11b693 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b693 15 11).toInstrSpec (add_r64_r64_effect_step 0x11b693 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x11b696 [0x49, 0x11, 0xD6] (fun s => s.RIP = 0x11b696) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b696 14 2))
      [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 14, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b696 14 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b696 0x49 0xd6 c (by decide) (by decide))) pre_rip
  have f67 : InstrSpec 0x11b699 [0x4C, 0x89, 0xF8] (fun s => s.RIP = 0x11b699) (movR64R64Effect 0x11b699 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b699 0 15).toInstrSpec (mov_r64_r64_effect_step 0x11b699 0x4c 0xf8 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x11b69c [0x4D, 0x89, 0xE0] (fun s => s.RIP = 0x11b69c) (movR64R64Effect 0x11b69c 8 12)
      [.gpr 12] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x11b69c 8 12).toInstrSpec (mov_r64_r64_effect_step 0x11b69c 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x11b69f [0x4C, 0x89, 0x64, 0x24, 0x20] (StorePre 0x11b69f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b69f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b69f 12 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b69f 12 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x11b69f 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x11b6a4 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x11b6a4) (mulR64Effect 0x11b6a4 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b6a4 12).toInstrSpec (mul_r64_effect_step 0x11b6a4 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x11b6a7 [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x11b6a7) (movR64R64Effect 0x11b6a7 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11b6a7 1 0).toInstrSpec (mov_r64_r64_effect_step 0x11b6a7 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x11b6aa [0x49, 0x89, 0xD3] (fun s => s.RIP = 0x11b6aa) (movR64R64Effect 0x11b6aa 11 2)
      [.gpr 2] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x11b6aa 11 2).toInstrSpec (mov_r64_r64_effect_step 0x11b6aa 0x49 0xd3 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x11b6ad [0x4D, 0x89, 0xF4] (fun s => s.RIP = 0x11b6ad) (movR64R64Effect 0x11b6ad 12 14)
      [.gpr 14] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x11b6ad 12 14).toInstrSpec (mov_r64_r64_effect_step 0x11b6ad 0x4d 0xf4 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x11b6b0 [0x49, 0x01, 0xFC] (fun s => s.RIP = 0x11b6b0) (addR64R64Effect 0x11b6b0 12 7)
      [.gpr 12, .gpr 7] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b6b0 12 7).toInstrSpec (add_r64_r64_effect_step 0x11b6b0 0x49 0xfc (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x11b6b3 [0x41, 0xBA, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11b6b3) (movR32Imm32Effect 0x11b6b3 6 10 0x0)
      [] [] [.reg 10, .rip] :=
    (movR32Imm32Effect_footprint 0x11b6b3 6 10 0x0).toInstrSpec (mov_r32_imm32_rex_effect_step 0x11b6b3 0x41 0xba (by decide) (by decide) 0x0) pre_rip
  have f76 : InstrSpec 0x11b6b9 [0x4D, 0x0F, 0x42, 0xD0] (fun s => s.RIP = 0x11b6b9) (atFlags (condHolds 2) (cmovR64R64Effect 0x11b6b9 4 10 8))
      [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (cmovR64R64Effect_footprint 0x11b6b9 4 10 8 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11b6b9 2 0x4d (by decide) 0xd0 (by decide) c)) pre_rip
  have f77 : InstrSpec 0x11b6bd [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x11b6bd) (movR64R64Effect 0x11b6bd 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b6bd 0 12).toInstrSpec (mov_r64_r64_effect_step 0x11b6bd 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x11b6c0 [0x49, 0xF7, 0xE0] (fun s => s.RIP = 0x11b6c0) (mulR64Effect 0x11b6c0 8)
      [.gpr 8, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b6c0 8).toInstrSpec (mul_r64_effect_step 0x11b6c0 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x11b6c3 [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x11b6c3) (movR64R64Effect 0x11b6c3 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x11b6c3 13 2).toInstrSpec (mov_r64_r64_effect_step 0x11b6c3 0x49 0xd5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 192) f60 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 193) (ρ' := [(0, 191), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b686) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f61 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 191), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 161), (15, 194), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b689) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f62 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 191), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 196), (15, 194), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b68c) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f63 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 199) f63 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 200) (ρ' := [(0, 191), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 196), (15, 198), (16, 199), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b68f) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f64 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 191), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 201), (15, 198), (16, 199), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b693) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f65 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 204) f65 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 205) (ρ' := [(0, 191), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 201), (15, 203), (16, 204), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b696) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f66 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 191), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b699) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f67 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 208), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b69c) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f68 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 208), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b69f) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.exec (n := 212) (ρ' := [(0, 208), (1, 84), (2, 192), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6a4) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f70 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 214) f70 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 215) (ρ' := [(0, 213), (1, 84), (2, 214), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6a7) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f71 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 213), (1, 216), (2, 214), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6aa) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f72 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 213), (1, 216), (2, 214), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 187), (11, 218), (12, 73), (13, 77), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6ad) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f73 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 213), (1, 216), (2, 214), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 187), (11, 218), (12, 220), (13, 77), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6b0) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f74 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 223) f74 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 224) (ρ' := [(0, 213), (1, 216), (2, 214), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 187), (11, 218), (12, 222), (13, 77), (14, 206), (15, 203), (16, 223), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6b3) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f75 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 213), (1, 216), (2, 214), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 225), (11, 218), (12, 222), (13, 77), (14, 206), (15, 203), (16, 223), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6b9) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f76 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 213), (1, 216), (2, 214), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 77), (14, 206), (15, 203), (16, 223), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6bd) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f77 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 229), (1, 216), (2, 214), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 77), (14, 206), (15, 203), (16, 223), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6c0) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 232) f78 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 233) (ρ' := [(0, 231), (1, 216), (2, 232), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 77), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6c3) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f79 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 231), (1, 216), (2, 232), (3, 100), (4, 4), (6, 184), (7, 140), (8, 210), (9, 144), (10, 227), (11, 218), (12, 222), (13, 234), (14, 206), (15, 203), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b6c6) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b5ba_4 code

theorem rest_l11b5ba_2 [Bindings] (code : CodeMap) :
    Rest (n := 144) code lifted (codeRange 0x11b5ba bytes_l11b5ba) [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 137), (10, 142), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (16, 138), (22, 22), (39, 39), (50, 50), (51, 51)]
      156 0x11b644 bytes_l11b5ba_2 b_l11b5ba_2 := by
  have f40 : InstrSpec 0x11b644 [0x4D, 0x01, 0xF1] (fun s => s.RIP = 0x11b644) (addR64R64Effect 0x11b644 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b644 9 14).toInstrSpec (add_r64_r64_effect_step 0x11b644 0x4d 0xf1 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x11b647 [0x49, 0x11, 0xD2] (fun s => s.RIP = 0x11b647) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b647 10 2))
      [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b647 10 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b647 0x49 0xd2 c (by decide) (by decide))) pre_rip
  have f42 : InstrSpec 0x11b64a [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x11b64a) (xorR32R32Effect 0x11b64a 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b64a 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b64a 0x45 0xff (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x11b64d [0x4C, 0x03, 0x56, 0x18] (LoadPre 0x11b64d (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11b64d + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x11b64d 10 (.base 6 (.d8 0x18)))
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (addR64M64Effect_footprint 0x11b64d 10 (.base 6 (.d8 0x18))).toInstrSpec (add_r64_m64_effect_step 0x11b64d 0x4c (by decide) 2 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f44 : InstrSpec 0x11b651 [0x41, 0x0F, 0x92, 0xC7] (fun s => s.RIP = 0x11b651) (atFlags (condHolds 2) (setccR8Effect 0x11b651 4 15))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .rip] :=
    (setccR8Effect_footprint 0x11b651 4 15 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b651 2 0x41 (by decide) 0xc7 (by decide) c)) pre_rip
  have f45 : InstrSpec 0x11b655 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x11b655) (movR64R64Effect 0x11b655 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b655 0 7).toInstrSpec (mov_r64_r64_effect_step 0x11b655 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x11b658 [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x11b658) (mulR64Effect 0x11b658 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b658 12).toInstrSpec (mul_r64_effect_step 0x11b658 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x11b65b [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x11b65b) (movR64R64Effect 0x11b65b 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x11b65b 14 2).toInstrSpec (mov_r64_r64_effect_step 0x11b65b 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x11b65e [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x11b65e) (movR64R64Effect 0x11b65e 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11b65e 6 0).toInstrSpec (mov_r64_r64_effect_step 0x11b65e 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x11b661 [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x11b661) (movR64R64Effect 0x11b661 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b661 0 11).toInstrSpec (mov_r64_r64_effect_step 0x11b661 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x11b664 [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x11b664) (mulR64Effect 0x11b664 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b664 13).toInstrSpec (mul_r64_effect_step 0x11b664 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x11b667 [0x4C, 0x01, 0xF2] (fun s => s.RIP = 0x11b667) (addR64R64Effect 0x11b667 2 14)
      [.gpr 2, .gpr 14] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b667 2 14).toInstrSpec (add_r64_r64_effect_step 0x11b667 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x11b66a [0x4C, 0x01, 0xD6] (fun s => s.RIP = 0x11b66a) (addR64R64Effect 0x11b66a 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b66a 6 10).toInstrSpec (add_r64_r64_effect_step 0x11b66a 0x4c 0xd6 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x11b66d [0x4C, 0x11, 0xFA] (fun s => s.RIP = 0x11b66d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b66d 2 15))
      [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b66d 2 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b66d 0x4c 0xfa c (by decide) (by decide))) pre_rip
  have f54 : InstrSpec 0x11b670 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x11b670) (xorR32R32Effect 0x11b670 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b670 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b670 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x11b673 [0x48, 0x01, 0xC6] (fun s => s.RIP = 0x11b673) (addR64R64Effect 0x11b673 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b673 6 0).toInstrSpec (add_r64_r64_effect_step 0x11b673 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x11b676 [0x41, 0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x11b676) (atFlags (condHolds 2) (setccR8Effect 0x11b676 4 10))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (setccR8Effect_footprint 0x11b676 4 10 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b676 2 0x41 (by decide) 0xc2 (by decide) c)) pre_rip
  have f57 : InstrSpec 0x11b67a [0x4C, 0x01, 0xC6] (fun s => s.RIP = 0x11b67a) (addR64R64Effect 0x11b67a 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b67a 6 8).toInstrSpec (add_r64_r64_effect_step 0x11b67a 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x11b67d [0x49, 0x11, 0xD2] (fun s => s.RIP = 0x11b67d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b67d 10 2))
      [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b67d 10 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b67d 0x49 0xd2 c (by decide) (by decide))) pre_rip
  have f59 : InstrSpec 0x11b680 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x11b680) (movR64R64Effect 0x11b680 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b680 0 7).toInstrSpec (mov_r64_r64_effect_step 0x11b680 0x48 0xf8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f40 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 145) f40 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 146) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 144), (10, 142), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (16, 145), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b647) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f41 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 144), (10, 147), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b64a) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f42 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 144), (10, 147), (11, 105), (12, 73), (13, 77), (14, 53), (15, 149), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b64d) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f43 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 152) f43 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 153) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 53), (15, 149), (16, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b651) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f44 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 53), (15, 154), (16, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b655) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 156), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 53), (15, 154), (16, 152), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b658) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f46 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 159) f46 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 160) (ρ' := [(0, 158), (1, 84), (2, 159), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 53), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b65b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f47 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 158), (1, 84), (2, 159), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b65e) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f48 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 158), (1, 84), (2, 159), (3, 100), (4, 4), (6, 163), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b661) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 165), (1, 84), (2, 159), (3, 100), (4, 4), (6, 163), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b664) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f50 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 168) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 169) (ρ' := [(0, 167), (1, 84), (2, 168), (3, 100), (4, 4), (6, 163), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b667) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f51 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 167), (1, 84), (2, 170), (3, 100), (4, 4), (6, 163), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b66a) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f52 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 173) f52 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 174) (ρ' := [(0, 167), (1, 84), (2, 170), (3, 100), (4, 4), (6, 172), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (16, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b66d) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 167), (1, 84), (2, 175), (3, 100), (4, 4), (6, 172), (7, 140), (8, 55), (9, 144), (10, 151), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b670) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f54 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 167), (1, 84), (2, 175), (3, 100), (4, 4), (6, 172), (7, 140), (8, 55), (9, 144), (10, 177), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b673) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f55 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 180) f55 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 181) (ρ' := [(0, 167), (1, 84), (2, 175), (3, 100), (4, 4), (6, 179), (7, 140), (8, 55), (9, 144), (10, 177), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (16, 180), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b676) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f56 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 167), (1, 84), (2, 175), (3, 100), (4, 4), (6, 179), (7, 140), (8, 55), (9, 144), (10, 182), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (16, 180), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b67a) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f57 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 185) f57 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 186) (ρ' := [(0, 167), (1, 84), (2, 175), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 182), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (16, 185), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b67d) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f58 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 167), (1, 84), (2, 175), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b680) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f59 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 189), (1, 84), (2, 175), (3, 100), (4, 4), (6, 184), (7, 140), (8, 55), (9, 144), (10, 187), (11, 105), (12, 73), (13, 77), (14, 161), (15, 154), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b683) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b5ba_3 code

theorem rest_l11b5ba_1 [Bindings] (code : CodeMap) :
    Rest (n := 98) code lifted (codeRange 0x11b5ba bytes_l11b5ba) [(0, 81), (1, 84), (2, 91), (3, 95), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 93), (12, 73), (13, 77), (14, 53), (15, 15), (16, 96), (22, 22), (39, 39), (50, 50), (51, 51)]
      176 0x11b602 bytes_l11b5ba_1 b_l11b5ba_1 := by
  have f20 : InstrSpec 0x11b602 [0x41, 0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x11b602) (atFlags (condHolds 2) (setccR8Effect 0x11b602 4 10))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (setccR8Effect_footprint 0x11b602 4 10 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b602 2 0x41 (by decide) 0xc2 (by decide) c)) pre_rip
  have f21 : InstrSpec 0x11b606 [0x48, 0x01, 0xC3] (fun s => s.RIP = 0x11b606) (addR64R64Effect 0x11b606 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b606 3 0).toInstrSpec (add_r64_r64_effect_step 0x11b606 0x48 0xc3 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11b609 [0x49, 0x11, 0xD2] (fun s => s.RIP = 0x11b609) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b609 10 2))
      [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b609 10 2).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b609 0x49 0xd2 c (by decide) (by decide))) pre_rip
  have f23 : InstrSpec 0x11b60c [0x4C, 0x8B, 0x5E, 0x30] (LoadPre 0x11b60c (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x11b60c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b60c 11 (.base 6 (.d8 0x30)))
      [.gpr 6] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x11b60c 11 (.base 6 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x11b60c 0x4c (by decide) 3 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x11b610 [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x11b610) (xorR32R32Effect 0x11b610 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b610 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b610 0x45 0xff (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x11b613 [0x4C, 0x03, 0x56, 0x10] (LoadPre 0x11b613 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11b613 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x11b613 10 (.base 6 (.d8 0x10)))
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (addR64M64Effect_footprint 0x11b613 10 (.base 6 (.d8 0x10))).toInstrSpec (add_r64_m64_effect_step 0x11b613 0x4c (by decide) 2 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x11b617 [0x41, 0x0F, 0x92, 0xC7] (fun s => s.RIP = 0x11b617) (atFlags (condHolds 2) (setccR8Effect 0x11b617 4 15))
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 15, .rip] :=
    (setccR8Effect_footprint 0x11b617 4 15 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b617 2 0x41 (by decide) 0xc7 (by decide) c)) pre_rip
  have f27 : InstrSpec 0x11b61b [0x4C, 0x89, 0xD8] (fun s => s.RIP = 0x11b61b) (movR64R64Effect 0x11b61b 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b61b 0 11).toInstrSpec (mov_r64_r64_effect_step 0x11b61b 0x4c 0xd8 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x11b61e [0x49, 0xF7, 0xE4] (fun s => s.RIP = 0x11b61e) (mulR64Effect 0x11b61e 12)
      [.gpr 12, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b61e 12).toInstrSpec (mul_r64_effect_step 0x11b61e 0x49 0xe4 (by decide) (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x11b621 [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x11b621) (movR64R64Effect 0x11b621 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11b621 7 2).toInstrSpec (mov_r64_r64_effect_step 0x11b621 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x11b624 [0x49, 0x89, 0xC1] (fun s => s.RIP = 0x11b624) (movR64R64Effect 0x11b624 9 0)
      [.gpr 0] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x11b624 9 0).toInstrSpec (mov_r64_r64_effect_step 0x11b624 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x11b627 [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x11b627) (movR64R64Effect 0x11b627 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b627 0 8).toInstrSpec (mov_r64_r64_effect_step 0x11b627 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x11b62a [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x11b62a) (mulR64Effect 0x11b62a 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b62a 13).toInstrSpec (mul_r64_effect_step 0x11b62a 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x11b62d [0x48, 0x01, 0xFA] (fun s => s.RIP = 0x11b62d) (addR64R64Effect 0x11b62d 2 7)
      [.gpr 2, .gpr 7] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b62d 2 7).toInstrSpec (add_r64_r64_effect_step 0x11b62d 0x48 0xfa (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x11b630 [0x4D, 0x01, 0xD1] (fun s => s.RIP = 0x11b630) (addR64R64Effect 0x11b630 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b630 9 10).toInstrSpec (add_r64_r64_effect_step 0x11b630 0x4d 0xd1 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x11b633 [0x4C, 0x11, 0xFA] (fun s => s.RIP = 0x11b633) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b633 2 15))
      [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b633 2 15).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b633 0x4c 0xfa c (by decide) (by decide))) pre_rip
  have f36 : InstrSpec 0x11b636 [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x11b636) (xorR32R32Effect 0x11b636 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b636 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b636 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x11b639 [0x49, 0x01, 0xC1] (fun s => s.RIP = 0x11b639) (addR64R64Effect 0x11b639 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b639 9 0).toInstrSpec (add_r64_r64_effect_step 0x11b639 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x11b63c [0x48, 0x8B, 0x7E, 0x38] (LoadPre 0x11b63c (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x11b63c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b63c 7 (.base 6 (.d8 0x38)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11b63c 7 (.base 6 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x11b63c 0x48 (by decide) 7 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x11b640 [0x41, 0x0F, 0x92, 0xC2] (fun s => s.RIP = 0x11b640) (atFlags (condHolds 2) (setccR8Effect 0x11b640 4 10))
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 10, .rip] :=
    (setccR8Effect_footprint 0x11b640 4 10 2).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x11b640 2 0x41 (by decide) 0xc2 (by decide) c)) pre_rip
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f20 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 95), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 98), (12, 73), (13, 77), (14, 53), (15, 15), (16, 96), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b606) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f21 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 101) f21 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 102) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 100), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 98), (12, 73), (13, 77), (14, 53), (15, 15), (16, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b609) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f22 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 100), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 103), (12, 73), (13, 77), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b60c) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f23 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 100), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 103), (11, 105), (12, 73), (13, 77), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b610) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f24 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 100), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 103), (11, 105), (12, 73), (13, 77), (14, 53), (15, 107), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b613) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f25 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 110) f25 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 111) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 100), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 107), (16, 110), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b617) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f26 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 100), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (16, 110), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b61b) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 114), (1, 84), (2, 91), (3, 100), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (16, 110), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b61e) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 117) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 118) (ρ' := [(0, 116), (1, 84), (2, 117), (3, 100), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b621) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 116), (1, 84), (2, 117), (3, 100), (4, 4), (6, 6), (7, 119), (8, 55), (9, 75), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b624) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f30 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 116), (1, 84), (2, 117), (3, 100), (4, 4), (6, 6), (7, 119), (8, 55), (9, 121), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b627) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 123), (1, 84), (2, 117), (3, 100), (4, 4), (6, 6), (7, 119), (8, 55), (9, 121), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b62a) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f32 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 126) f32 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 127) (ρ' := [(0, 125), (1, 84), (2, 126), (3, 100), (4, 4), (6, 6), (7, 119), (8, 55), (9, 121), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b62d) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 125), (1, 84), (2, 128), (3, 100), (4, 4), (6, 6), (7, 119), (8, 55), (9, 121), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b630) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f34 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 131) f34 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 132) (ρ' := [(0, 125), (1, 84), (2, 128), (3, 100), (4, 4), (6, 6), (7, 119), (8, 55), (9, 130), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (16, 131), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b633) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 119), (8, 55), (9, 130), (10, 109), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b636) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f36 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 119), (8, 55), (9, 130), (10, 135), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b639) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f37 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 138) f37 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 139) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 119), (8, 55), (9, 137), (10, 135), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (16, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b63c) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f38 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 137), (10, 135), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (16, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b640) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f39 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 125), (1, 84), (2, 133), (3, 100), (4, 4), (6, 6), (7, 140), (8, 55), (9, 137), (10, 142), (11, 105), (12, 73), (13, 77), (14, 53), (15, 112), (16, 138), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b644) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b5ba_2 code

theorem rest_l11b5ba [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11b5ba bytes_l11b5ba) (entryMap (live .l11b5ba))
      196 0x11b5ba bytes_l11b5ba b_l11b5ba := by
  have f0 : InstrSpec 0x11b5ba [0x4C, 0x8B, 0x76, 0x20] (LoadPre 0x11b5ba (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x11b5ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b5ba 14 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x11b5ba 14 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11b5ba 0x4c (by decide) 6 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11b5be [0x4C, 0x8B, 0x46, 0x28] (LoadPre 0x11b5be (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x11b5be + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b5be 8 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x11b5be 8 (.base 6 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x11b5be 0x4c (by decide) 0 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11b5c2 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x11b5c2) (movR64R64Effect 0x11b5c2 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b5c2 0 14).toInstrSpec (mov_r64_r64_effect_step 0x11b5c2 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11b5c5 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x11b5c5) (mulR64Effect 0x11b5c5 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b5c5 9).toInstrSpec (mul_r64_effect_step 0x11b5c5 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11b5c8 [0x48, 0x89, 0xD3] (fun s => s.RIP = 0x11b5c8) (movR64R64Effect 0x11b5c8 3 2)
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11b5c8 3 2).toInstrSpec (mov_r64_r64_effect_step 0x11b5c8 0x48 0xd3 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x11b5cb [0x48, 0x89, 0xC1] (fun s => s.RIP = 0x11b5cb) (movR64R64Effect 0x11b5cb 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11b5cb 1 0).toInstrSpec (mov_r64_r64_effect_step 0x11b5cb 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11b5ce [0x4C, 0x89, 0xC0] (fun s => s.RIP = 0x11b5ce) (movR64R64Effect 0x11b5ce 0 8)
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b5ce 0 8).toInstrSpec (mov_r64_r64_effect_step 0x11b5ce 0x4c 0xc0 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11b5d1 [0x49, 0xF7, 0xE1] (fun s => s.RIP = 0x11b5d1) (mulR64Effect 0x11b5d1 9)
      [.gpr 9, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b5d1 9).toInstrSpec (mul_r64_effect_step 0x11b5d1 0x49 0xe1 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11b5d4 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x11b5d4) (movR64R64Effect 0x11b5d4 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11b5d4 7 0).toInstrSpec (mov_r64_r64_effect_step 0x11b5d4 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11b5d7 [0x4D, 0x89, 0xCC] (fun s => s.RIP = 0x11b5d7) (movR64R64Effect 0x11b5d7 12 9)
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x11b5d7 12 9).toInstrSpec (mov_r64_r64_effect_step 0x11b5d7 0x4d 0xcc (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11b5da [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x11b5da) (movR64R64Effect 0x11b5da 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x11b5da 9 2).toInstrSpec (mov_r64_r64_effect_step 0x11b5da 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11b5dd [0x49, 0xBD, 0xC4, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45] (fun s => s.RIP = 0x11b5dd) (movR64Imm64Effect 0x11b5dd 13 0x4551231950b75fc4)
      [] [] [.reg 13, .rip] :=
    (movR64Imm64Effect_footprint 0x11b5dd 13 0x4551231950b75fc4).toInstrSpec (mov_r64_imm64_effect_step 0x11b5dd 0x49 0xbd (by decide) (by decide) 0x4551231950b75fc4) pre_rip
  have f12 : InstrSpec 0x11b5e7 [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x11b5e7) (movR64R64Effect 0x11b5e7 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11b5e7 0 14).toInstrSpec (mov_r64_r64_effect_step 0x11b5e7 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11b5ea [0x49, 0xF7, 0xE5] (fun s => s.RIP = 0x11b5ea) (mulR64Effect 0x11b5ea 13)
      [.gpr 13, .gpr 0] [] [.reg 0, .reg 2, .flags, .rip] :=
    (mulR64Effect_footprint 0x11b5ea 13).toInstrSpec (mul_r64_effect_step 0x11b5ea 0x49 0xe5 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11b5ed [0x48, 0x03, 0x0E] (LoadPre 0x11b5ed (fun s => AddrMode.addr (.base 6 .none) s (0x11b5ed + BitVec.ofNat 64 3)) 8) (addR64M64Effect 0x11b5ed 1 (.base 6 .none))
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (addR64M64Effect_footprint 0x11b5ed 1 (.base 6 .none)).toInstrSpec (add_r64_m64_effect_step 0x11b5ed 0x48 (by decide) 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x11b5f0 [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x11b5f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b5f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b5f0 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b5f0 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11b5f0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x11b5f5 [0x48, 0x13, 0x5E, 0x08] (LoadPre 0x11b5f5 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11b5f5 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11b5f5 3 (.base 6 (.d8 0x8))))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 6] [.CF] [.reg 3, .flags, .rip] :=
    (adcR64M64Effect_footprint 0x11b5f5 3 (.base 6 (.d8 0x8))).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_m64_effect_step 0x11b5f5 0x48 (by decide) 3 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide) c)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x11b5f9 [0x4C, 0x11, 0xCA] (fun s => s.RIP = 0x11b5f9) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b5f9 2 9))
      [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .flags, .rip] :=
    (adcR64R64Effect_footprint 0x11b5f9 2 9).toInstrSpec (StepEffect.atFlags fun c => (adc_r64_r64_effect_step 0x11b5f9 0x4c 0xca c (by decide) (by decide))) pre_rip
  have f18 : InstrSpec 0x11b5fc [0x45, 0x31, 0xD2] (fun s => s.RIP = 0x11b5fc) (xorR32R32Effect 0x11b5fc 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x11b5fc 3 10 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x11b5fc 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x11b5ff [0x48, 0x01, 0xFB] (fun s => s.RIP = 0x11b5ff) (addR64R64Effect 0x11b5ff 3 7)
      [.gpr 3, .gpr 7] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11b5ff 3 7).toInstrSpec (add_r64_r64_effect_step 0x11b5ff 0x48 0xfb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (6, 6), (9, 9), (10, 10), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5be) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (6, 6), (8, 55), (9, 9), (10, 10), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5c2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (4, 4), (6, 6), (8, 55), (9, 9), (10, 10), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5c5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 59), (2, 60), (4, 4), (6, 6), (8, 55), (9, 9), (10, 10), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5c8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (2, 60), (3, 62), (4, 4), (6, 6), (8, 55), (9, 9), (10, 10), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5cb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 64), (2, 60), (3, 62), (4, 4), (6, 6), (8, 55), (9, 9), (10, 10), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5ce) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 64), (2, 60), (3, 62), (4, 4), (6, 6), (8, 55), (9, 9), (10, 10), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5d1) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 69) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 70) (ρ' := [(0, 68), (1, 64), (2, 69), (3, 62), (4, 4), (6, 6), (8, 55), (9, 9), (10, 10), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5d4) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 68), (1, 64), (2, 69), (3, 62), (4, 4), (6, 6), (7, 71), (8, 55), (9, 9), (10, 10), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5d7) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 68), (1, 64), (2, 69), (3, 62), (4, 4), (6, 6), (7, 71), (8, 55), (9, 9), (10, 10), (12, 73), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5da) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 68), (1, 64), (2, 69), (3, 62), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 10), (12, 73), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5dd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 68), (1, 64), (2, 69), (3, 62), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 10), (12, 73), (13, 77), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5e7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 64), (2, 69), (3, 62), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 10), (12, 73), (13, 77), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5ea) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 82) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 64), (2, 82), (3, 62), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 10), (12, 73), (13, 77), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5ed) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 85) f14 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 86) (ρ' := [(0, 81), (1, 84), (2, 82), (3, 62), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 10), (12, 73), (13, 77), (14, 53), (15, 15), (16, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5f0) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 81), (1, 84), (2, 82), (3, 62), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 10), (12, 73), (13, 77), (14, 53), (15, 15), (16, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5f5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f16 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 89) f16 .CF (fun _ => rfl) (adcR64M64Effect_fresh 0x11b5f5 3 (.base 6 (.d8 0x8)) _ (.head _)) rfl rfl ?_
  refine RestInside.exec (n := 90) (ρ' := [(0, 81), (1, 84), (2, 82), (3, 88), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 10), (12, 73), (13, 77), (14, 53), (15, 15), (16, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5f9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 88), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 10), (12, 73), (13, 77), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5fc) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f18 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 88), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 93), (12, 73), (13, 77), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b5ff) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f19 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 96) f19 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 97) (ρ' := [(0, 81), (1, 84), (2, 91), (3, 95), (4, 4), (6, 6), (7, 71), (8, 55), (9, 75), (10, 93), (12, 73), (13, 77), (14, 53), (15, 15), (16, 96), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b602) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b5ba_1 code

theorem block_l11b5ba [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11b5ba :=
  Rest.liftedBlock (rest_l11b5ba code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11b5ba x hx)

theorem rest_l11b864 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11b864 bytes_l11b864) (entryMap (live .l11b864))
      4 0x11b864 bytes_l11b864 b_l11b864 := by
  have f0 : InstrSpec 0x11b864 [0x88, 0x44, 0x24, 0x18] (StorePre 0x11b864 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b864 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11b864 4 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11b864 4 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_effect_step 0x11b864 0 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11b868 [0x49, 0xC1, 0xED, 0x3F] (fun s => s.RIP = 0x11b868) (shrR64Effect 0x11b868 4 13 63)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR64Effect_footprint 0x11b868 4 13 63).toInstrSpec (shr_r64_imm8_effect_step 0x11b868 0x49 0xed 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11b86c [0x44, 0x89, 0xEF] (fun s => s.RIP = 0x11b86c) (movR32R32Effect 0x11b86c 3 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11b86c 3 7 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x11b86c 0x44 0xef (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11b86f [0xE8, 0xDC, 0xC4, 0x00, 0x00] (PushPre 0x11b86f 5) (callEffect (fun _ => 0x127d50) 0x11b874)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11b86f 0x127d50 0x11b874).toInstrSpec (call_rel32_effect_step 0x11b86f 0xc4dc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b868) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b86c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b86f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 60) (by decide) (by decide) rfl rfl

theorem block_l11b864 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11b864 :=
  Rest.liftedBlock (rest_l11b864 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11b864 x hx)

theorem rest_l11b874 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11b874 bytes_l11b874) (entryMap (live .l11b874))
      4 0x11b874 bytes_l11b874 b_l11b874 := by
  have f0 : InstrSpec 0x11b874 [0xF6, 0xD0] (fun s => s.RIP = 0x11b874) (notR8Effect 0x11b874 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR8Effect_footprint 0x11b874 2 0).toInstrSpec (not_r8_effect_step 0x11b874 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11b876 [0x24, 0x01] (fun s => s.RIP = 0x11b876) (andAlImm8Effect 0x11b876 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andAlImm8Effect_footprint 0x11b876 0x1).toInstrSpec (and_al_imm8_effect_step 0x11b876 0x1) pre_rip
  have f2 : InstrSpec 0x11b878 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x11b878) (movzxR32R8Effect 0x11b878 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x11b878 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x11b878 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11b87b [0xE8, 0xD0, 0xC4, 0x00, 0x00] (PushPre 0x11b87b 5) (callEffect (fun _ => 0x127d50) 0x11b880)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11b87b 0x127d50 0x11b880).toInstrSpec (call_rel32_effect_step 0x11b87b 0xc4d0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b876) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b878) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b87b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l11b874 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11b874 :=
  Rest.liftedBlock (rest_l11b874 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11b874 x hx)

theorem rest_l11b880 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11b880 bytes_l11b880) (entryMap (live .l11b880))
      3 0x11b880 bytes_l11b880 b_l11b880 := by
  have f0 : InstrSpec 0x11b880 [0x0A, 0x44, 0x24, 0x18] (LoadPre 0x11b880 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b880 + BitVec.ofNat 64 4)) 1) (orR8M8Effect 0x11b880 4 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR8M8Effect_footprint 0x11b880 4 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (or_r8_m8_effect_step 0x11b880 0 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11b884 [0x0F, 0xB6, 0xF8] (fun s => s.RIP = 0x11b884) (movzxR32R8Effect 0x11b884 3 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x11b884 3 7 0).toInstrSpec (movzx_r32_r8_effect_step 0x11b884 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11b887 [0xE8, 0xC4, 0xC4, 0x00, 0x00] (PushPre 0x11b887 5) (callEffect (fun _ => 0x127d50) 0x11b88c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11b887 0x127d50 0x11b88c).toInstrSpec (call_rel32_effect_step 0x11b887 0xc4c4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b884) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b887) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l11b880 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11b880 :=
  Rest.liftedBlock (rest_l11b880 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11b880 x hx)

theorem rest_l11b88c_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x11b88c bytes_l11b88c) [(0, 79), (1, 63), (2, 69), (3, 77), (4, 85), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      7 0x11b8d9 bytes_l11b88c_1 b_l11b88c_1 := by
  have f20 : InstrSpec 0x11b8d9 [0x5B] (PopPre 0x11b8d9) (popR64Effect 0x11b8d9 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11b8d9 1 3).toInstrSpec (pop_r64_effect_step 0x11b8d9 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f21 : InstrSpec 0x11b8da [0x41, 0x5C] (PopPre 0x11b8da) (popR64Effect 0x11b8da 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11b8da 2 12).toInstrSpec (pop_r64_rex_effect_step 0x11b8da 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f22 : InstrSpec 0x11b8dc [0x41, 0x5D] (PopPre 0x11b8dc) (popR64Effect 0x11b8dc 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11b8dc 2 13).toInstrSpec (pop_r64_rex_effect_step 0x11b8dc 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f23 : InstrSpec 0x11b8de [0x41, 0x5E] (PopPre 0x11b8de) (popR64Effect 0x11b8de 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11b8de 2 14).toInstrSpec (pop_r64_rex_effect_step 0x11b8de 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f24 : InstrSpec 0x11b8e0 [0x41, 0x5F] (PopPre 0x11b8e0) (popR64Effect 0x11b8e0 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11b8e0 2 15).toInstrSpec (pop_r64_rex_effect_step 0x11b8e0 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f25 : InstrSpec 0x11b8e2 [0x5D] (PopPre 0x11b8e2) (popR64Effect 0x11b8e2 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11b8e2 1 5).toInstrSpec (pop_r64_effect_step 0x11b8e2 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f26 : InstrSpec 0x11b8e3 [0xC3] (RetPre 0x11b8e3) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11b8e3).toInstrSpec (ret_effect_step 0x11b8e3) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f20 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 88) f20 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 89) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 87), (4, 88), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8da) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 91) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 92) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 87), (4, 91), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 90), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8dc) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f22 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 94) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 95) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 87), (4, 94), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 90), (13, 93), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8de) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 97) f23 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 98) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 87), (4, 97), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 90), (13, 93), (14, 96), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8e0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f24 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 100) f24 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 101) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 87), (4, 100), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 90), (13, 93), (14, 96), (15, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8e2) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 103) f25 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 104) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 87), (4, 103), (5, 102), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 90), (13, 93), (14, 96), (15, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8e3) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 106) f26 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 107) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 87), (4, 106), (5, 102), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 90), (13, 93), (14, 96), (15, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) f26 (by decide) rfl rfl rfl (by decide)

theorem rest_l11b88c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11b88c bytes_l11b88c) (entryMap (live .l11b88c))
      27 0x11b88c bytes_l11b88c b_l11b88c := by
  have f0 : InstrSpec 0x11b88c [0x88, 0x44, 0x24, 0x08] (StorePre 0x11b88c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b88c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11b88c 4 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11b88c 4 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x11b88c 0 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x11b890 [0x48, 0x8D, 0x44, 0x24, 0x08] (fun s => s.RIP = 0x11b890) (leaR64Effect 0x11b890 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x11b890 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x11b890 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11b895 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x11b895 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b895 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11b895 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11b895 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x11b895 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11b89a [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x11b89a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b89a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b89a 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11b89a 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11b89a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11b89f [0x48, 0x8B, 0x54, 0x24, 0x20] (LoadPre 0x11b89f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b89f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b89f 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11b89f 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x11b89f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11b8a4 [0x84, 0xC0] (fun s => s.RIP = 0x11b8a4) (testR8R8Effect 0x11b8a4 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11b8a4 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11b8a4 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11b8a6 [0x48, 0x0F, 0x45, 0xCA] (fun s => s.RIP = 0x11b8a6) (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8a6 4 1 2))
      [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x11b8a6 4 1 2 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11b8a6 5 0x48 (by decide) 0xca (by decide) c)) pre_rip
  have f7 : InstrSpec 0x11b8aa [0x48, 0x8B, 0x54, 0x24, 0x38] (LoadPre 0x11b8aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11b8aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b8aa 2 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11b8aa 2 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x11b8aa 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11b8af [0x84, 0xC0] (fun s => s.RIP = 0x11b8af) (testR8R8Effect 0x11b8af 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11b8af 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11b8af 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11b8b1 [0x49, 0x0F, 0x45, 0xD4] (fun s => s.RIP = 0x11b8b1) (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8b1 4 2 12))
      [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x11b8b1 4 2 12 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11b8b1 5 0x49 (by decide) 0xd4 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x11b8b5 [0x84, 0xC0] (fun s => s.RIP = 0x11b8b5) (testR8R8Effect 0x11b8b5 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11b8b5 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11b8b5 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11b8b7 [0x4D, 0x0F, 0x45, 0xFE] (fun s => s.RIP = 0x11b8b7) (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8b7 4 15 14))
      [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 15, .rip] :=
    (cmovR64R64Effect_footprint 0x11b8b7 4 15 14 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11b8b7 5 0x4d (by decide) 0xfe (by decide) c)) pre_rip
  have f12 : InstrSpec 0x11b8bb [0x84, 0xC0] (fun s => s.RIP = 0x11b8bb) (testR8R8Effect 0x11b8bb 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x11b8bb 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x11b8bb 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11b8bd [0x48, 0x0F, 0x45, 0xDD] (fun s => s.RIP = 0x11b8bd) (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8bd 4 3 5))
      [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 3, .rip] :=
    (cmovR64R64Effect_footprint 0x11b8bd 4 3 5 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x11b8bd 5 0x48 (by decide) 0xdd (by decide) c)) pre_rip
  have f14 : InstrSpec 0x11b8c1 [0x48, 0x8B, 0x44, 0x24, 0x40] (LoadPre 0x11b8c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11b8c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b8c1 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11b8c1 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x11b8c1 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x11b8c6 [0x48, 0x89, 0x08] (StorePre 0x11b8c6 3 (fun s => AddrMode.addr (.base 0 .none) s (0x11b8c6 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11b8c6 1 (.base 0 .none))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b8c6 1 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11b8c6 0x48 (by decide) 1 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x11b8c9 [0x48, 0x89, 0x50, 0x08] (StorePre 0x11b8c9 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x11b8c9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11b8c9 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b8c9 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11b8c9 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x11b8cd [0x4C, 0x89, 0x78, 0x10] (StorePre 0x11b8cd 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x11b8cd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11b8cd 15 (.base 0 (.d8 0x10)))
      [.gpr 15, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b8cd 15 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11b8cd 0x4c (by decide) 7 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x11b8d1 [0x48, 0x89, 0x58, 0x18] (StorePre 0x11b8d1 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x11b8d1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11b8d1 3 (.base 0 (.d8 0x18)))
      [.gpr 3, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11b8d1 3 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11b8d1 0x48 (by decide) 3 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11b8d5 [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x11b8d5) (addR64Imm8Effect 0x11b8d5 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11b8d5 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x11b8d5 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b890) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b895) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b89a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b89f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8a4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 57), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8a6) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 63), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8aa) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 63), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8af) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 63), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8b1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 63), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8b5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 63), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8b7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 63), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8bb) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 63), (2, 69), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8bd) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 63), (2, 69), (3, 77), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8c1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 77), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8c6) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 77), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8c9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 77), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8cd) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 77), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8d1) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 77), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8d5) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 79), (1, 63), (2, 69), (3, 77), (4, 85), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11b8d9) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11b88c_1 code

theorem block_l11b88c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11b88c :=
  Rest.liftedBlock (rest_l11b88c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11b88c x hx)

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

theorem_by block_l11b510_eval :
    program.runBlock (dialect code) ⟨.l11b510, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11b53b_eval :
    program.runBlock (dialect code) ⟨.l11b53b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11b5a3_eval :
    program.runBlock (dialect code) ⟨.l11b5a3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11b5ba_eval :
    program.runBlock (dialect code) ⟨.l11b5ba, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11b864_eval :
    program.runBlock (dialect code) ⟨.l11b864, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11b874_eval :
    program.runBlock (dialect code) ⟨.l11b874, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11b880_eval :
    program.runBlock (dialect code) ⟨.l11b880, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11b88c_eval :
    program.runBlock (dialect code) ⟨.l11b88c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
