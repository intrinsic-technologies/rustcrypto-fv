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

theorem rest_l100510 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100510 bytes_l100510) (entryMap (live .l100510))
      11 0x100510 bytes_l100510 b_l100510 := by
  have f0 : InstrSpec 0x100510 [0x55] (PushPre 0x100510 1) (pushR64Effect 0x100510 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100510 1 5).toInstrSpec (push_r64_effect_step 0x100510 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x100511 [0x41, 0x57] (PushPre 0x100511 2) (pushR64Effect 0x100511 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100511 2 15).toInstrSpec (push_r64_rex_effect_step 0x100511 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x100513 [0x41, 0x56] (PushPre 0x100513 2) (pushR64Effect 0x100513 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100513 2 14).toInstrSpec (push_r64_rex_effect_step 0x100513 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100515 [0x41, 0x55] (PushPre 0x100515 2) (pushR64Effect 0x100515 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100515 2 13).toInstrSpec (push_r64_rex_effect_step 0x100515 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100517 [0x41, 0x54] (PushPre 0x100517 2) (pushR64Effect 0x100517 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100517 2 12).toInstrSpec (push_r64_rex_effect_step 0x100517 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100519 [0x53] (PushPre 0x100519 1) (pushR64Effect 0x100519 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x100519 1 3).toInstrSpec (push_r64_effect_step 0x100519 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10051a [0x48, 0x81, 0xEC, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10051a) (subR64Imm32Effect 0x10051a 4 0xb8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10051a 4 0xb8).toInstrSpec (sub_r64_imm32_effect_step 0x10051a 0x48 0xec 0xb8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100521 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x100521) (movR64R64Effect 0x100521 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x100521 14 6).toInstrSpec (mov_r64_r64_effect_step 0x100521 0x49 0xf6 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x100524 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x100524) (movR64R64Effect 0x100524 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x100524 3 7).toInstrSpec (mov_r64_r64_effect_step 0x100524 0x48 0xfb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x100527 [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x100527) (leaR64Effect 0x100527 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100527 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x100527 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10052c [0xE8, 0xCF, 0x63, 0x00, 0x00] (PushPre 0x10052c 5) (callEffect (fun _ => 0x106900) 0x100531)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10052c 0x106900 0x100531).toInstrSpec (call_rel32_effect_step 0x10052c 0x63cf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100511) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100513) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100515) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100517) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100519) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10051a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100521) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100524) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(3, 69), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100527) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(3, 69), (4, 65), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10052c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(3, 69), (4, 73), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106900) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 75) (by decide) (by decide) rfl rfl

theorem block_l100510 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100510 :=
  Rest.liftedBlock (rest_l100510 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100510 x hx)

theorem rest_l100531 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100531 bytes_l100531) (entryMap (live .l100531))
      5 0x100531 bytes_l100531 b_l100531 := by
  have f0 : InstrSpec 0x100531 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x100531 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100531 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100531 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100531 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x100531 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100535 [0x4C, 0x8B, 0x7C, 0x24, 0x14] (LoadPre 0x100535 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100535 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100535 15 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x100535 15 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x100535 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10053a [0x0F, 0xB6, 0x6C, 0x24, 0x1C] (LoadPre 0x10053a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10053a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10053a 5 5 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x10053a 5 5 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (movzx_r32_m8_effect_step 0x10053a 5 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10053f [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x10053f) (cmpR32Imm8Effect 0x10053f 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x10053f 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x10053f 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100535) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10053a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10053f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100542) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x100542 5 0x3e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100531 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100531 :=
  Rest.liftedBlock (rest_l100531 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100531 x hx)

theorem rest_l100544 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100544 bytes_l100544) (entryMap (live .l100544))
      3 0x100544 bytes_l100544 b_l100544 := by
  have f0 : InstrSpec 0x100544 [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x100544) (leaR64Effect 0x100544 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100544 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x100544 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100549 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x100549) (movR64R64Effect 0x100549 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100549 6 14).toInstrSpec (mov_r64_r64_effect_step 0x100549 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10054c [0xE8, 0xCF, 0x5B, 0x00, 0x00] (PushPre 0x10054c 5) (callEffect (fun _ => 0x106120) 0x100551)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10054c 0x106120 0x100551).toInstrSpec (call_rel32_effect_step 0x10054c 0x5bcf (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100549) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10054c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106120) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l100544 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100544 :=
  Rest.liftedBlock (rest_l100544 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100544 x hx)

theorem rest_l100551 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100551 bytes_l100551) (entryMap (live .l100551))
      4 0x100551 bytes_l100551 b_l100551 := by
  have f0 : InstrSpec 0x100551 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x100551 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100551 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100551 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100551 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x100551 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100555 [0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x100555 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100555 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100555 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x100555 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x100555 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100559 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x100559) (cmpR32Imm8Effect 0x100559 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x100559 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x100559 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100555) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100559) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10055c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x10055c 5 0x84) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100551 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100551 :=
  Rest.liftedBlock (rest_l100551 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100551 x hx)

theorem rest_l100562 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100562 bytes_l100562) (entryMap (live .l100562))
      10 0x100562 bytes_l100562 b_l100562 := by
  have f0 : InstrSpec 0x100562 [0x89, 0xEA] (fun s => s.RIP = 0x100562) (movR32R32Effect 0x100562 2 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x100562 2 2 5).toInstrSpec (mov_r32_r32_effect_step 0x100562 0xea (by decide)) pre_rip
  have f1 : InstrSpec 0x100564 [0x80, 0xE2, 0x01] (fun s => s.RIP = 0x100564) (andR8Imm8Effect 0x100564 3 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x100564 3 2 0x1).toInstrSpec (and_r8_imm8_effect_step 0x100564 0xe2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100567 [0x4D, 0x89, 0xF8] (fun s => s.RIP = 0x100567) (movR64R64Effect 0x100567 8 15)
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x100567 8 15).toInstrSpec (mov_r64_r64_effect_step 0x100567 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10056a [0x49, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x10056a) (shrR64Effect 0x10056a 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10056a 4 8 32).toInstrSpec (shr_r64_imm8_effect_step 0x10056a 0x49 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10056e [0x89, 0xCD] (fun s => s.RIP = 0x10056e) (movR32R32Effect 0x10056e 2 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x10056e 2 5 1).toInstrSpec (mov_r32_r32_effect_step 0x10056e 0xcd (by decide)) pre_rip
  have f5 : InstrSpec 0x100570 [0x89, 0xCF] (fun s => s.RIP = 0x100570) (movR32R32Effect 0x100570 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x100570 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x100570 0xcf (by decide)) pre_rip
  have f6 : InstrSpec 0x100572 [0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x100572) (shrR32Effect 0x100572 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x100572 3 7 8).toInstrSpec (shr_r32_imm8_effect_step 0x100572 0xef 0x8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100575 [0xB8, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100575) (movR32Imm32Effect 0x100575 5 0 0x2)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x100575 5 0 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x100575 0xb8 (by decide) 0x2) pre_rip
  have f8 : InstrSpec 0x10057a [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x10057a) (movR32R32Effect 0x10057a 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10057a 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x10057a 0x44 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100564) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100567) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10056a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10056e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 61), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100570) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 61), (7, 63), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100572) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 61), (7, 65), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100575) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 55), (3, 3), (4, 4), (5, 61), (7, 65), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10057a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 69), (2, 55), (3, 3), (4, 4), (5, 61), (7, 65), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10057d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 71) (jmp_rel32_effect_step 0x10057d 0xe4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100562 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100562 :=
  Rest.liftedBlock (rest_l100562 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100562 x hx)

theorem rest_l100582 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100582 bytes_l100582) (entryMap (live .l100582))
      19 0x100582 bytes_l100582 b_l100582 := by
  have f0 : InstrSpec 0x100582 [0x0F, 0xB6, 0x4C, 0x24, 0x1F] (LoadPre 0x100582 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x100582 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100582 5 1 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x100582 5 1 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (movzx_r32_m8_effect_step 0x100582 1 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100587 [0xC1, 0xE1, 0x10] (fun s => s.RIP = 0x100587) (shlR32Effect 0x100587 3 1 16)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x100587 3 1 16).toInstrSpec (shl_r32_imm8_effect_step 0x100587 0xe1 0x10 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10058a [0x0F, 0xB7, 0x7C, 0x24, 0x1D] (LoadPre 0x10058a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x10058a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10058a 5 7 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x10058a 5 7 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m16_effect_step 0x10058a 7 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10058f [0x09, 0xCF] (fun s => s.RIP = 0x10058f) (orR32R32Effect 0x10058f 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10058f 2 7 1).toInstrSpec (or_r32_r32_effect_step 0x10058f 0xcf (by decide)) pre_rip
  have f4 : InstrSpec 0x100591 [0x0F, 0xB6, 0x54, 0x24, 0x20] (LoadPre 0x100591 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100591 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100591 5 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x100591 5 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x100591 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100596 [0x48, 0x8B, 0x4C, 0x24, 0x21] (LoadPre 0x100596 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x100596 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100596 1 (.sib 4 none 0 (.d8 0x21)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100596 1 (.sib 4 none 0 (.d8 0x21))).toInstrSpec (mov_r64_m64_effect_step 0x100596 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10059b [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10059b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10059b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10059b 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10059b 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x10059b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1005a3 [0x48, 0x8B, 0x4C, 0x24, 0x29] (LoadPre 0x1005a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x1005a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005a3 1 (.sib 4 none 0 (.d8 0x29)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1005a3 1 (.sib 4 none 0 (.d8 0x29))).toInstrSpec (mov_r64_m64_effect_step 0x1005a3 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1005a8 [0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x1005a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1005a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1005a8 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1005a8 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x1005a8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1005b0 [0x48, 0x8B, 0x4C, 0x24, 0x31] (LoadPre 0x1005b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1005b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005b0 1 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1005b0 1 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (mov_r64_m64_effect_step 0x1005b0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1005b5 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1005b5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1005b5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1005b5 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1005b5 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1005b5 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1005bd [0x48, 0x8B, 0x4C, 0x24, 0x39] (LoadPre 0x1005bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x1005bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005bd 1 (.sib 4 none 0 (.d8 0x39)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1005bd 1 (.sib 4 none 0 (.d8 0x39))).toInstrSpec (mov_r64_m64_effect_step 0x1005bd 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1005c2 [0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1005c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1005c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1005c2 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1005c2 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x1005c2 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1005ca [0x48, 0x8B, 0x4C, 0x24, 0x40] (LoadPre 0x1005ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1005ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005ca 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1005ca 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1005ca 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1005cf [0x48, 0x89, 0x8C, 0x24, 0x9F, 0x00, 0x00, 0x00] (StorePre 0x1005cf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1005cf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1005cf 1 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1005cf 1 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (mov_m64_r64_effect_step 0x1005cf 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1005d7 [0x4D, 0x89, 0xF8] (fun s => s.RIP = 0x1005d7) (movR64R64Effect 0x1005d7 8 15)
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1005d7 8 15).toInstrSpec (mov_r64_r64_effect_step 0x1005d7 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1005da [0x49, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x1005da) (shrR64Effect 0x1005da 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x1005da 4 8 32).toInstrSpec (shr_r64_imm8_effect_step 0x1005da 0x49 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1005de [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x1005de) (movR32R32Effect 0x1005de 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1005de 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1005de 0x44 0xf9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100587) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10058a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10058f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100591) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100596) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10059b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005a3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 66), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005a8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 66), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005b0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005b5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 69), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005bd) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 72), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005c2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 72), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005ca) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005cf) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005d7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005da) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (8, 80), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005de) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (8, 80), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005e1) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 84) (jmp_rel32_effect_step 0x1005e1 0x80 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100582 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100582 :=
  Rest.liftedBlock (rest_l100582 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100582 x hx)

theorem rest_l1005e6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1005e6 bytes_l1005e6) (entryMap (live .l1005e6))
      3 0x1005e6 bytes_l1005e6 b_l1005e6 := by
  have f0 : InstrSpec 0x1005e6 [0x0F, 0xB6, 0x54, 0x24, 0x18] (LoadPre 0x1005e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1005e6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1005e6 5 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1005e6 5 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x1005e6 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1005eb [0x80, 0xFA, 0x0D] (fun s => s.RIP = 0x1005eb) (cmpR8Imm8Effect 0x1005eb 3 2 0xd)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1005eb 3 2 0xd).toInstrSpec (cmp_r8_imm8_effect_step 0x1005eb 0xfa 0xd (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005eb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005ee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1005ee 5 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1005e6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1005e6 :=
  Rest.liftedBlock (rest_l1005e6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1005e6 x hx)

theorem rest_l1005f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1005f0 bytes_l1005f0) (entryMap (live .l1005f0))
      5 0x1005f0 bytes_l1005f0 b_l1005f0 := by
  have f0 : InstrSpec 0x1005f0 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1005f0 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1005f0 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1005f0 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1005f0 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1005f0 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1005f5 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x1005f5 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1005f5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1005f5 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x1005f5 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1005f5 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1005f9 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1005f9) (movR32Imm32Effect 0x1005f9 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1005f9 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1005f9 0xb8 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x1005fe [0xB2, 0x05] (fun s => s.RIP = 0x1005fe) (movR8Imm8Effect 0x1005fe 2 2 0x5)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR8Imm8Effect_footprint 0x1005fe 2 2 0x5).toInstrSpec (mov_r8_imm8_effect_step 0x1005fe 0xb2 (by decide) 0x5) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005f9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 54), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1005fe) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100600) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 60) (jmp_rel8_effect_step 0x100600 0x5 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1005f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1005f0 :=
  Rest.liftedBlock (rest_l1005f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1005f0 x hx)

theorem rest_l100602 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100602 bytes_l100602) (entryMap (live .l100602))
      1 0x100602 bytes_l100602 b_l100602 := by
  have f0 : InstrSpec 0x100602 [0x4C, 0x8B, 0x7C, 0x24, 0x1C] (LoadPre 0x100602 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100602 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100602 15 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x100602 15 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x100602 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100607) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l100602 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100602 :=
  Rest.liftedBlock (rest_l100602 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100602 x hx)

theorem rest_l100607 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100607 bytes_l100607) (entryMap (live .l100607))
      18 0x100607 bytes_l100607 b_l100607 := by
  have f0 : InstrSpec 0x100607 [0x88, 0x54, 0x24, 0x18] (StorePre 0x100607 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100607 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100607 4 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x100607 4 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_effect_step 0x100607 2 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10060b [0x4C, 0x89, 0x7C, 0x24, 0x1C] (StorePre 0x10060b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10060b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10060b 15 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10060b 15 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x10060b 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100610 [0x44, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x100610 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100610 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100610 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x100610 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x100610 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100615 [0x44, 0x89, 0xFF] (fun s => s.RIP = 0x100615) (movR32R32Effect 0x100615 3 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x100615 3 7 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x100615 0x44 0xff (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100618 [0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x100618) (shrR32Effect 0x100618 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x100618 3 7 8).toInstrSpec (shr_r32_imm8_effect_step 0x100618 0xef 0x8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10061b [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x10061b) (movR64R64Effect 0x10061b 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10061b 2 15).toInstrSpec (mov_r64_r64_effect_step 0x10061b 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10061e [0x48, 0xC1, 0xEA, 0x20] (fun s => s.RIP = 0x10061e) (shrR64Effect 0x10061e 4 2 32)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10061e 4 2 32).toInstrSpec (shr_r64_imm8_effect_step 0x10061e 0x48 0xea 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100622 [0x48, 0x8B, 0x74, 0x24, 0x29] (LoadPre 0x100622 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x100622 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100622 6 (.sib 4 none 0 (.d8 0x29)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100622 6 (.sib 4 none 0 (.d8 0x29))).toInstrSpec (mov_r64_m64_effect_step 0x100622 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100627 [0x4C, 0x8B, 0x4C, 0x24, 0x31] (LoadPre 0x100627 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x100627 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100627 9 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x100627 9 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (mov_r64_m64_effect_step 0x100627 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10062c [0x48, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10062c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10062c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10062c 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10062c 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x10062c 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100634 [0x4C, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x100634 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100634 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100634 9 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100634 9 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x100634 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10063c [0x48, 0x8B, 0x74, 0x24, 0x39] (LoadPre 0x10063c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x10063c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10063c 6 (.sib 4 none 0 (.d8 0x39)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10063c 6 (.sib 4 none 0 (.d8 0x39))).toInstrSpec (mov_r64_m64_effect_step 0x10063c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x100641 [0x48, 0x89, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x100641 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100641 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100641 6 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100641 6 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x100641 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x100649 [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x100649 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100649 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100649 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100649 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x100649 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10064e [0x48, 0x89, 0xB4, 0x24, 0x9F, 0x00, 0x00, 0x00] (StorePre 0x10064e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x10064e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10064e 6 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10064e 6 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (mov_m64_r64_effect_step 0x10064e 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x100656 [0x48, 0x8B, 0x74, 0x24, 0x21] (LoadPre 0x100656 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x100656 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100656 6 (.sib 4 none 0 (.d8 0x21)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100656 6 (.sib 4 none 0 (.d8 0x21))).toInstrSpec (mov_r64_m64_effect_step 0x100656 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10065b [0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10065b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10065b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10065b 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10065b 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x10065b 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x100663 [0x44, 0x89, 0xFD] (fun s => s.RIP = 0x100663) (movR32R32Effect 0x100663 3 5 15)
      [.gpr 15] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x100663 3 5 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x100663 0x44 0xfd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10060b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100610) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100615) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 57), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100618) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 59), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10061b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (7, 59), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10061e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (7, 59), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100622) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 65), (7, 59), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100627) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 65), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10062c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 65), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100634) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 65), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10063c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 71), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100641) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 71), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100649) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 74), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10064e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 74), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100656) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 77), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10065b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 77), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100663) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 80), (6, 77), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100666) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 82) (by decide) rfl

theorem block_l100607 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100607 :=
  Rest.liftedBlock (rest_l100607 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100607 x hx)

theorem rest_l100666 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100666 bytes_l100666) (entryMap (live .l100666))
      12 0x100666 bytes_l100666 b_l100666 := by
  have f0 : InstrSpec 0x100666 [0x49, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x100666) (shlR64Effect 0x100666 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x100666 4 8 32).toInstrSpec (shl_r64_imm8_effect_step 0x100666 0x49 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10066a [0x89, 0xCE] (fun s => s.RIP = 0x10066a) (movR32R32Effect 0x10066a 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10066a 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x10066a 0xce (by decide)) pre_rip
  have f2 : InstrSpec 0x10066c [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x10066c) (orR64R64Effect 0x10066c 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10066c 6 8).toInstrSpec (or_r64_r64_effect_step 0x10066c 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10066f [0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x10066f) (shlR32Effect 0x10066f 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10066f 3 7 8).toInstrSpec (shl_r32_imm8_effect_step 0x10066f 0xe7 0x8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100672 [0x44, 0x0F, 0xB6, 0xC5] (fun s => s.RIP = 0x100672) (movzxR32R8Effect 0x100672 4 8 5)
      [.gpr 5] [] [.reg 8, .rip] :=
    (movzxR32R8Effect_footprint 0x100672 4 8 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x100672 0x44 (by decide) 0xc5 (by decide)) pre_rip
  have f5 : InstrSpec 0x100676 [0x41, 0x09, 0xF8] (fun s => s.RIP = 0x100676) (orR32R32Effect 0x100676 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (orR32R32Effect_footprint 0x100676 3 8 7).toInstrSpec (or_r32_r32_rex_effect_step 0x100676 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100679 [0x0F, 0xB7, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x100679 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100679 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x100679 8 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x100679 8 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m16_effect_step 0x100679 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x100681 [0x66, 0x89, 0x7C, 0x24, 0x0C] (StorePre 0x100681 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100681 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100681 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x100681 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x100681 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100686 [0x0F, 0xB6, 0xBC, 0x24, 0x82, 0x00, 0x00, 0x00] (LoadPre 0x100686 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x100686 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100686 8 7 (.sib 4 none 0 (.d32 0x82)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x100686 8 7 (.sib 4 none 0 (.d32 0x82))).toInstrSpec (movzx_r32_m8_effect_step 0x100686 7 (.sib 4 none 0 (.d32 0x82)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10068e [0x40, 0x88, 0x7C, 0x24, 0x0E] (StorePre 0x10068e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10068e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10068e 5 7 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10068e 5 7 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10068e 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100693 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x100693) (cmpR32Imm8Effect 0x100693 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x100693 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x100693 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10066a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10066c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10066f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100672) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100676) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100679) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 65), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100681) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 65), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100686) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10068e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100693) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100696) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel32_effect_step 0x100696 5 0x283) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100666 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100666 :=
  Rest.liftedBlock (rest_l100666 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100666 x hx)

theorem rest_l10069c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10069c bytes_l10069c) (entryMap (live .l10069c))
      10 0x10069c bytes_l10069c b_l10069c := by
  have f0 : InstrSpec 0x10069c [0x48, 0x89, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x10069c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10069c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10069c 6 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10069c 6 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x10069c 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1006a4 [0x44, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x1006a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1006a4 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1006a4 8 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1006a4 8 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m32_r32_effect_step 0x1006a4 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1006ac [0x88, 0x94, 0x24, 0xB4, 0x00, 0x00, 0x00] (StorePre 0x1006ac 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x1006ac + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1006ac 7 2 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1006ac 7 2 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (mov_m8_r8_effect_step 0x1006ac 2 (by decide) (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1006b3 [0x0F, 0xB7, 0x44, 0x24, 0x0C] (LoadPre 0x1006b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1006b3 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1006b3 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1006b3 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x1006b3 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1006b8 [0x66, 0x89, 0x84, 0x24, 0xB5, 0x00, 0x00, 0x00] (StorePre 0x1006b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb5)) s (0x1006b8 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1006b8 8 0 (.sib 4 none 0 (.d32 0xb5)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1006b8 8 0 (.sib 4 none 0 (.d32 0xb5))).toInstrSpec (mov_m16_r16_effect_step 0x1006b8 0 (.sib 4 none 0 (.d32 0xb5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1006c0 [0x0F, 0xB6, 0x44, 0x24, 0x0E] (LoadPre 0x1006c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1006c0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1006c0 5 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1006c0 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x1006c0 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1006c5 [0x88, 0x84, 0x24, 0xB7, 0x00, 0x00, 0x00] (StorePre 0x1006c5 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x1006c5 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1006c5 7 0 (.sib 4 none 0 (.d32 0xb7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1006c5 7 0 (.sib 4 none 0 (.d32 0xb7))).toInstrSpec (mov_m8_r8_effect_step 0x1006c5 0 (by decide) (.sib 4 none 0 (.d32 0xb7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1006cc [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x1006cc) (leaR64Effect 0x1006cc 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1006cc 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1006cc 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1006d1 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1006d1) (movR32Imm32Effect 0x1006d1 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1006d1 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1006d1 0xba (by decide) 0x1) pre_rip
  have f9 : InstrSpec 0x1006d6 [0xE8, 0xF5, 0x6F, 0x02, 0x00] (PushPre 0x1006d6 5) (callEffect (fun _ => 0x1276d0) 0x1006db)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1006d6 0x1276d0 0x1006db).toInstrSpec (call_rel32_effect_step 0x1006d6 0x26ff5 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006a4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006ac) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006b3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006b8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006c0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006c5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006cc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006d1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 1), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006d6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 1), (2, 64), (3, 3), (4, 66), (5, 5), (6, 6), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d0) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l10069c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10069c :=
  Rest.liftedBlock (rest_l10069c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10069c x hx)

theorem rest_l1006db [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1006db bytes_l1006db) (entryMap (live .l1006db))
      3 0x1006db bytes_l1006db b_l1006db := by
  have f0 : InstrSpec 0x1006db [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1006db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1006db + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1006db 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1006db 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x1006db 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1006df [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1006df) (cmpR32Imm8Effect 0x1006df 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1006df 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1006df 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006df) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006e2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1006e2 5 0x299) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1006db [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1006db :=
  Rest.liftedBlock (rest_l1006db code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1006db x hx)

theorem rest_l1006e8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1006e8 bytes_l1006e8) (entryMap (live .l1006e8))
      4 0x1006e8 bytes_l1006e8 b_l1006e8 := by
  have f0 : InstrSpec 0x1006e8 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x1006e8) (leaR64Effect 0x1006e8 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1006e8 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x1006e8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1006ed [0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1006ed) (leaR64Effect 0x1006ed 2 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1006ed 2 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (lea_r64_effect_step 0x1006ed 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1006f5 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1006f5) (movR64R64Effect 0x1006f5 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1006f5 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1006f5 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1006f8 [0xE8, 0xB3, 0x31, 0x00, 0x00] (PushPre 0x1006f8 5) (callEffect (fun _ => 0x1038b0) 0x1006fd)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1006f8 0x1038b0 0x1006fd).toInstrSpec (call_rel32_effect_step 0x1006f8 0x31b3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006ed) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006f5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1006f8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1006e8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1006e8 :=
  Rest.liftedBlock (rest_l1006e8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1006e8 x hx)

theorem rest_l1006fd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1006fd bytes_l1006fd) (entryMap (live .l1006fd))
      3 0x1006fd bytes_l1006fd b_l1006fd := by
  have f0 : InstrSpec 0x1006fd [0x8B, 0x44, 0x24, 0x48] (LoadPre 0x1006fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1006fd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1006fd 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1006fd 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x1006fd 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100701 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x100701) (cmpR32Imm8Effect 0x100701 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x100701 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x100701 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100701) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100704) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x100704 5 0x2bd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1006fd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1006fd :=
  Rest.liftedBlock (rest_l1006fd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1006fd x hx)

theorem rest_l10070a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10070a bytes_l10070a) (entryMap (live .l10070a))
      5 0x10070a bytes_l10070a b_l10070a := by
  have f0 : InstrSpec 0x10070a [0x4C, 0x8B, 0x7C, 0x24, 0x50] (LoadPre 0x10070a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10070a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10070a 15 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x10070a 15 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x10070a 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10070f [0x4C, 0x8B, 0x64, 0x24, 0x58] (LoadPre 0x10070f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10070f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10070f 12 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10070f 12 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x10070f 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100714 [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x100714) (leaR64Effect 0x100714 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100714 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x100714 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x100719 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x100719) (movR64R64Effect 0x100719 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100719 6 14).toInstrSpec (mov_r64_r64_effect_step 0x100719 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10071c [0xE8, 0xDF, 0x61, 0x00, 0x00] (PushPre 0x10071c 5) (callEffect (fun _ => 0x106900) 0x100721)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10071c 0x106900 0x100721).toInstrSpec (call_rel32_effect_step 0x10071c 0x61df (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10070f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100714) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100719) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10071c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106900) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10070a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10070a :=
  Rest.liftedBlock (rest_l10070a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10070a x hx)

theorem rest_l100721 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100721 bytes_l100721) (entryMap (live .l100721))
      5 0x100721 bytes_l100721 b_l100721 := by
  have f0 : InstrSpec 0x100721 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x100721 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100721 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100721 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100721 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x100721 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100725 [0x4C, 0x8B, 0x6C, 0x24, 0x14] (LoadPre 0x100725 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100725 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100725 13 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x100725 13 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x100725 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10072a [0x0F, 0xB6, 0x6C, 0x24, 0x1C] (LoadPre 0x10072a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10072a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10072a 5 5 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x10072a 5 5 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (movzx_r32_m8_effect_step 0x10072a 5 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10072f [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x10072f) (cmpR32Imm8Effect 0x10072f 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x10072f 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x10072f 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100725) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10072a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10072f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100732) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x100732 5 0x3e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100721 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100721 :=
  Rest.liftedBlock (rest_l100721 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100721 x hx)

theorem rest_l100734 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100734 bytes_l100734) (entryMap (live .l100734))
      3 0x100734 bytes_l100734 b_l100734 := by
  have f0 : InstrSpec 0x100734 [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x100734) (leaR64Effect 0x100734 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x100734 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x100734 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100739 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x100739) (movR64R64Effect 0x100739 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x100739 6 14).toInstrSpec (mov_r64_r64_effect_step 0x100739 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10073c [0xE8, 0xDF, 0x59, 0x00, 0x00] (PushPre 0x10073c 5) (callEffect (fun _ => 0x106120) 0x100741)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10073c 0x106120 0x100741).toInstrSpec (call_rel32_effect_step 0x10073c 0x59df (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100739) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10073c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106120) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l100734 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100734 :=
  Rest.liftedBlock (rest_l100734 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100734 x hx)

theorem rest_l100741 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100741 bytes_l100741) (entryMap (live .l100741))
      4 0x100741 bytes_l100741 b_l100741 := by
  have f0 : InstrSpec 0x100741 [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x100741 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100741 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100741 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x100741 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x100741 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100745 [0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x100745 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100745 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100745 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x100745 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x100745 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100749 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x100749) (cmpR32Imm8Effect 0x100749 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x100749 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x100749 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100745) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100749) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10074c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x10074c 5 0x84) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100741 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100741 :=
  Rest.liftedBlock (rest_l100741 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100741 x hx)

theorem rest_l100752 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100752 bytes_l100752) (entryMap (live .l100752))
      10 0x100752 bytes_l100752 b_l100752 := by
  have f0 : InstrSpec 0x100752 [0x89, 0xEA] (fun s => s.RIP = 0x100752) (movR32R32Effect 0x100752 2 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x100752 2 2 5).toInstrSpec (mov_r32_r32_effect_step 0x100752 0xea (by decide)) pre_rip
  have f1 : InstrSpec 0x100754 [0x80, 0xE2, 0x01] (fun s => s.RIP = 0x100754) (andR8Imm8Effect 0x100754 3 2 0x1)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x100754 3 2 0x1).toInstrSpec (and_r8_imm8_effect_step 0x100754 0xe2 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100757 [0x4D, 0x89, 0xE8] (fun s => s.RIP = 0x100757) (movR64R64Effect 0x100757 8 13)
      [.gpr 13] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x100757 8 13).toInstrSpec (mov_r64_r64_effect_step 0x100757 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10075a [0x49, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x10075a) (shrR64Effect 0x10075a 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x10075a 4 8 32).toInstrSpec (shr_r64_imm8_effect_step 0x10075a 0x49 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10075e [0x89, 0xCF] (fun s => s.RIP = 0x10075e) (movR32R32Effect 0x10075e 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x10075e 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x10075e 0xcf (by decide)) pre_rip
  have f5 : InstrSpec 0x100760 [0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x100760) (shrR32Effect 0x100760 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x100760 3 7 8).toInstrSpec (shr_r32_imm8_effect_step 0x100760 0xef 0x8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100763 [0xB8, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100763) (movR32Imm32Effect 0x100763 5 0 0x2)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x100763 5 0 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x100763 0xb8 (by decide) 0x2) pre_rip
  have f7 : InstrSpec 0x100768 [0x89, 0xCD] (fun s => s.RIP = 0x100768) (movR32R32Effect 0x100768 2 5 1)
      [.gpr 1] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x100768 2 5 1).toInstrSpec (mov_r32_r32_effect_step 0x100768 0xcd (by decide)) pre_rip
  have f8 : InstrSpec 0x10076a [0x44, 0x89, 0xE9] (fun s => s.RIP = 0x10076a) (movR32R32Effect 0x10076a 3 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10076a 3 1 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x10076a 0x44 0xe9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100754) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100757) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10075a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10075e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 61), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100760) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 63), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100763) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 63), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100768) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 1), (2, 55), (3, 3), (4, 4), (5, 67), (7, 63), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10076a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 69), (2, 55), (3, 3), (4, 4), (5, 67), (7, 63), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10076d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 71) (jmp_rel32_effect_step 0x10076d 0xe4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100752 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100752 :=
  Rest.liftedBlock (rest_l100752 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100752 x hx)

theorem rest_l100772 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100772 bytes_l100772) (entryMap (live .l100772))
      19 0x100772 bytes_l100772 b_l100772 := by
  have f0 : InstrSpec 0x100772 [0x0F, 0xB6, 0x4C, 0x24, 0x1F] (LoadPre 0x100772 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x100772 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100772 5 1 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x100772 5 1 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (movzx_r32_m8_effect_step 0x100772 1 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100777 [0xC1, 0xE1, 0x10] (fun s => s.RIP = 0x100777) (shlR32Effect 0x100777 3 1 16)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x100777 3 1 16).toInstrSpec (shl_r32_imm8_effect_step 0x100777 0xe1 0x10 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10077a [0x0F, 0xB7, 0x7C, 0x24, 0x1D] (LoadPre 0x10077a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x10077a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10077a 5 7 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x10077a 5 7 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m16_effect_step 0x10077a 7 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10077f [0x09, 0xCF] (fun s => s.RIP = 0x10077f) (orR32R32Effect 0x10077f 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10077f 2 7 1).toInstrSpec (or_r32_r32_effect_step 0x10077f 0xcf (by decide)) pre_rip
  have f4 : InstrSpec 0x100781 [0x0F, 0xB6, 0x54, 0x24, 0x20] (LoadPre 0x100781 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100781 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100781 5 2 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x100781 5 2 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x100781 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x100786 [0x48, 0x8B, 0x4C, 0x24, 0x21] (LoadPre 0x100786 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x100786 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100786 1 (.sib 4 none 0 (.d8 0x21)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100786 1 (.sib 4 none 0 (.d8 0x21))).toInstrSpec (mov_r64_m64_effect_step 0x100786 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10078b [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10078b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10078b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10078b 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10078b 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x10078b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x100793 [0x48, 0x8B, 0x4C, 0x24, 0x29] (LoadPre 0x100793 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x100793 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100793 1 (.sib 4 none 0 (.d8 0x29)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100793 1 (.sib 4 none 0 (.d8 0x29))).toInstrSpec (mov_r64_m64_effect_step 0x100793 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100798 [0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x100798 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100798 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100798 1 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100798 1 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x100798 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1007a0 [0x48, 0x8B, 0x4C, 0x24, 0x31] (LoadPre 0x1007a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1007a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1007a0 1 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1007a0 1 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (mov_r64_m64_effect_step 0x1007a0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1007a5 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x1007a5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1007a5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1007a5 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1007a5 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x1007a5 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1007ad [0x48, 0x8B, 0x4C, 0x24, 0x39] (LoadPre 0x1007ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x1007ad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1007ad 1 (.sib 4 none 0 (.d8 0x39)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1007ad 1 (.sib 4 none 0 (.d8 0x39))).toInstrSpec (mov_r64_m64_effect_step 0x1007ad 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1007b2 [0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x1007b2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1007b2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1007b2 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1007b2 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x1007b2 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1007ba [0x48, 0x8B, 0x4C, 0x24, 0x40] (LoadPre 0x1007ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1007ba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1007ba 1 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1007ba 1 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1007ba 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1007bf [0x48, 0x89, 0x8C, 0x24, 0x9F, 0x00, 0x00, 0x00] (StorePre 0x1007bf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1007bf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1007bf 1 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1007bf 1 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (mov_m64_r64_effect_step 0x1007bf 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1007c7 [0x4D, 0x89, 0xE8] (fun s => s.RIP = 0x1007c7) (movR64R64Effect 0x1007c7 8 13)
      [.gpr 13] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1007c7 8 13).toInstrSpec (mov_r64_r64_effect_step 0x1007c7 0x4d 0xe8 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1007ca [0x49, 0xC1, 0xE8, 0x20] (fun s => s.RIP = 0x1007ca) (shrR64Effect 0x1007ca 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR64Effect_footprint 0x1007ca 4 8 32).toInstrSpec (shr_r64_imm8_effect_step 0x1007ca 0x49 0xe8 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1007ce [0x44, 0x89, 0xE9] (fun s => s.RIP = 0x1007ce) (movR32R32Effect 0x1007ce 3 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1007ce 3 1 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x1007ce 0x44 0xe9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100777) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10077a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10077f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100781) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100786) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10078b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 63), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100793) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 66), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100798) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 66), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007a0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007a5) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 69), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007ad) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 72), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007b2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 72), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007ba) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007bf) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007c7) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007ca) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 75), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (8, 80), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007ce) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (8, 80), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007d1) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 84) (jmp_rel32_effect_step 0x1007d1 0x80 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100772 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100772 :=
  Rest.liftedBlock (rest_l100772 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100772 x hx)

theorem rest_l1007d6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1007d6 bytes_l1007d6) (entryMap (live .l1007d6))
      3 0x1007d6 bytes_l1007d6 b_l1007d6 := by
  have f0 : InstrSpec 0x1007d6 [0x0F, 0xB6, 0x54, 0x24, 0x18] (LoadPre 0x1007d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1007d6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1007d6 5 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x1007d6 5 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x1007d6 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1007db [0x80, 0xFA, 0x0D] (fun s => s.RIP = 0x1007db) (cmpR8Imm8Effect 0x1007db 3 2 0xd)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR8Imm8Effect_footprint 0x1007db 3 2 0xd).toInstrSpec (cmp_r8_imm8_effect_step 0x1007db 0xfa 0xd (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007db) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007de) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x1007de 5 0x12) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1007d6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1007d6 :=
  Rest.liftedBlock (rest_l1007d6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1007d6 x hx)

theorem rest_l1007e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1007e0 bytes_l1007e0) (entryMap (live .l1007e0))
      5 0x1007e0 bytes_l1007e0 b_l1007e0 := by
  have f0 : InstrSpec 0x1007e0 [0x41, 0xC6, 0x46, 0x20, 0x01] (StorePre 0x1007e0 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1007e0 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1007e0 (.base 14 (.d8 0x20)) 0x1)
      [.gpr 14] [] [.rip] :=
    (movM8Imm8RexEffect_footprint 0x1007e0 (.base 14 (.d8 0x20)) 0x1).toInstrSpec (mov_m8_imm8_rex_effect_step 0x1007e0 0x41 (by decide) (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1007e5 [0x41, 0x8B, 0x4E, 0x1C] (LoadPre 0x1007e5 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1007e5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1007e5 1 (.base 14 (.d8 0x1c)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32M32Effect_footprint 0x1007e5 1 (.base 14 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x1007e5 0x41 (by decide) 1 (.base 14 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1007e9 [0xB8, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1007e9) (movR32Imm32Effect 0x1007e9 5 0 0x1)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1007e9 5 0 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1007e9 0xb8 (by decide) 0x1) pre_rip
  have f3 : InstrSpec 0x1007ee [0xB2, 0x05] (fun s => s.RIP = 0x1007ee) (movR8Imm8Effect 0x1007ee 2 2 0x5)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movR8Imm8Effect_footprint 0x1007ee 2 2 0x5).toInstrSpec (mov_r8_imm8_effect_step 0x1007ee 0xb2 (by decide) 0x5) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(1, 54), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007e9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 54), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007ee) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007f0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 60) (jmp_rel8_effect_step 0x1007f0 0x5 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1007e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1007e0 :=
  Rest.liftedBlock (rest_l1007e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1007e0 x hx)

theorem rest_l1007f2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1007f2 bytes_l1007f2) (entryMap (live .l1007f2))
      1 0x1007f2 bytes_l1007f2 b_l1007f2 := by
  have f0 : InstrSpec 0x1007f2 [0x4C, 0x8B, 0x6C, 0x24, 0x1C] (LoadPre 0x1007f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1007f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1007f2 13 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x1007f2 13 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x1007f2 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007f7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1007f2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1007f2 :=
  Rest.liftedBlock (rest_l1007f2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1007f2 x hx)

theorem rest_l1007f7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1007f7 bytes_l1007f7) (entryMap (live .l1007f7))
      18 0x1007f7 bytes_l1007f7 b_l1007f7 := by
  have f0 : InstrSpec 0x1007f7 [0x88, 0x54, 0x24, 0x18] (StorePre 0x1007f7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1007f7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1007f7 4 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1007f7 4 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_effect_step 0x1007f7 2 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1007fb [0x4C, 0x89, 0x6C, 0x24, 0x1C] (StorePre 0x1007fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1007fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1007fb 13 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1007fb 13 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m64_r64_effect_step 0x1007fb 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x100800 [0x44, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x100800 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100800 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100800 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x100800 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x100800 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100805 [0x44, 0x89, 0xEF] (fun s => s.RIP = 0x100805) (movR32R32Effect 0x100805 3 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x100805 3 7 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x100805 0x44 0xef (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100808 [0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x100808) (shrR32Effect 0x100808 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x100808 3 7 8).toInstrSpec (shr_r32_imm8_effect_step 0x100808 0xef 0x8 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10080b [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x10080b) (movR64R64Effect 0x10080b 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10080b 2 13).toInstrSpec (mov_r64_r64_effect_step 0x10080b 0x4c 0xea (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10080e [0x48, 0xC1, 0xEA, 0x20] (fun s => s.RIP = 0x10080e) (shrR64Effect 0x10080e 4 2 32)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR64Effect_footprint 0x10080e 4 2 32).toInstrSpec (shr_r64_imm8_effect_step 0x10080e 0x48 0xea 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x100812 [0x48, 0x8B, 0x74, 0x24, 0x29] (LoadPre 0x100812 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x100812 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100812 6 (.sib 4 none 0 (.d8 0x29)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100812 6 (.sib 4 none 0 (.d8 0x29))).toInstrSpec (mov_r64_m64_effect_step 0x100812 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100817 [0x4C, 0x8B, 0x4C, 0x24, 0x31] (LoadPre 0x100817 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x100817 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100817 9 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x100817 9 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (mov_r64_m64_effect_step 0x100817 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10081c [0x48, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10081c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10081c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10081c 6 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10081c 6 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_m64_r64_effect_step 0x10081c 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100824 [0x4C, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x100824 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100824 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100824 9 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100824 9 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x100824 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10082c [0x48, 0x8B, 0x74, 0x24, 0x39] (LoadPre 0x10082c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x10082c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10082c 6 (.sib 4 none 0 (.d8 0x39)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10082c 6 (.sib 4 none 0 (.d8 0x39))).toInstrSpec (mov_r64_m64_effect_step 0x10082c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x100831 [0x48, 0x89, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x100831 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100831 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100831 6 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100831 6 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x100831 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x100839 [0x48, 0x8B, 0x74, 0x24, 0x40] (LoadPre 0x100839 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100839 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100839 6 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100839 6 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x100839 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10083e [0x48, 0x89, 0xB4, 0x24, 0x9F, 0x00, 0x00, 0x00] (StorePre 0x10083e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x10083e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10083e 6 (.sib 4 none 0 (.d32 0x9f)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10083e 6 (.sib 4 none 0 (.d32 0x9f))).toInstrSpec (mov_m64_r64_effect_step 0x10083e 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x9f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x100846 [0x48, 0x8B, 0x74, 0x24, 0x21] (LoadPre 0x100846 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x100846 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100846 6 (.sib 4 none 0 (.d8 0x21)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x100846 6 (.sib 4 none 0 (.d8 0x21))).toInstrSpec (mov_r64_m64_effect_step 0x100846 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10084b [0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x10084b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10084b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10084b 6 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10084b 6 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x10084b 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x100853 [0x44, 0x89, 0xED] (fun s => s.RIP = 0x100853) (movR32R32Effect 0x100853 3 5 13)
      [.gpr 13] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x100853 3 5 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x100853 0x44 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1007fb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100800) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100805) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 57), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100808) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 59), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10080b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (7, 59), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10080e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (7, 59), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100812) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 65), (7, 59), (8, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100817) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 65), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10081c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 65), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100824) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 65), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10082c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 71), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100831) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 71), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100839) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 74), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10083e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 74), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100846) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 77), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10084b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (6, 77), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100853) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f17 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 80), (6, 77), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100856) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 82) (by decide) rfl

theorem block_l1007f7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1007f7 :=
  Rest.liftedBlock (rest_l1007f7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1007f7 x hx)

theorem rest_l100856 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100856 bytes_l100856) (entryMap (live .l100856))
      12 0x100856 bytes_l100856 b_l100856 := by
  have f0 : InstrSpec 0x100856 [0x49, 0xC1, 0xE0, 0x20] (fun s => s.RIP = 0x100856) (shlR64Effect 0x100856 4 8 32)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64Effect_footprint 0x100856 4 8 32).toInstrSpec (shl_r64_imm8_effect_step 0x100856 0x49 0xe0 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10085a [0x89, 0xCE] (fun s => s.RIP = 0x10085a) (movR32R32Effect 0x10085a 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10085a 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x10085a 0xce (by decide)) pre_rip
  have f2 : InstrSpec 0x10085c [0x4C, 0x09, 0xC6] (fun s => s.RIP = 0x10085c) (orR64R64Effect 0x10085c 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (orR64R64Effect_footprint 0x10085c 6 8).toInstrSpec (or_r64_r64_effect_step 0x10085c 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10085f [0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x10085f) (shlR32Effect 0x10085f 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10085f 3 7 8).toInstrSpec (shl_r32_imm8_effect_step 0x10085f 0xe7 0x8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x100862 [0x44, 0x0F, 0xB6, 0xC5] (fun s => s.RIP = 0x100862) (movzxR32R8Effect 0x100862 4 8 5)
      [.gpr 5] [] [.reg 8, .rip] :=
    (movzxR32R8Effect_footprint 0x100862 4 8 5).toInstrSpec (movzx_r32_r8_rex_effect_step 0x100862 0x44 (by decide) 0xc5 (by decide)) pre_rip
  have f5 : InstrSpec 0x100866 [0x41, 0x09, 0xF8] (fun s => s.RIP = 0x100866) (orR32R32Effect 0x100866 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (orR32R32Effect_footprint 0x100866 3 8 7).toInstrSpec (or_r32_r32_rex_effect_step 0x100866 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x100869 [0x0F, 0xB7, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x100869 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100869 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x100869 8 7 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x100869 8 7 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m16_effect_step 0x100869 7 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x100871 [0x66, 0x89, 0x7C, 0x24, 0x0C] (StorePre 0x100871 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100871 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100871 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x100871 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x100871 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x100876 [0x0F, 0xB6, 0xBC, 0x24, 0x82, 0x00, 0x00, 0x00] (LoadPre 0x100876 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x100876 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100876 8 7 (.sib 4 none 0 (.d32 0x82)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x100876 8 7 (.sib 4 none 0 (.d32 0x82))).toInstrSpec (movzx_r32_m8_effect_step 0x100876 7 (.sib 4 none 0 (.d32 0x82)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10087e [0x40, 0x88, 0x7C, 0x24, 0x0E] (StorePre 0x10087e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10087e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10087e 5 7 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10087e 5 7 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10087e 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x100883 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x100883) (cmpR32Imm8Effect 0x100883 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x100883 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x100883 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10085a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10085c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10085f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100862) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100866) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 59), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100869) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 65), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100871) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 65), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100876) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10087e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100883) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100886) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 73) (jcc_rel32_effect_step 0x100886 5 0x93) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l100856 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100856 :=
  Rest.liftedBlock (rest_l100856 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100856 x hx)

theorem rest_l10088c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10088c bytes_l10088c) (entryMap (live .l10088c))
      10 0x10088c bytes_l10088c b_l10088c := by
  have f0 : InstrSpec 0x10088c [0x48, 0x89, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x10088c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10088c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10088c 6 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10088c 6 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x10088c 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x100894 [0x44, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x100894 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x100894 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100894 8 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100894 8 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m32_r32_effect_step 0x100894 0x44 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10089c [0x88, 0x94, 0x24, 0xB4, 0x00, 0x00, 0x00] (StorePre 0x10089c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x10089c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10089c 7 2 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10089c 7 2 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (mov_m8_r8_effect_step 0x10089c 2 (by decide) (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1008a3 [0x0F, 0xB7, 0x44, 0x24, 0x0C] (LoadPre 0x1008a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1008a3 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1008a3 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1008a3 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x1008a3 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1008a8 [0x66, 0x89, 0x84, 0x24, 0xB5, 0x00, 0x00, 0x00] (StorePre 0x1008a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb5)) s (0x1008a8 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1008a8 8 0 (.sib 4 none 0 (.d32 0xb5)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1008a8 8 0 (.sib 4 none 0 (.d32 0xb5))).toInstrSpec (mov_m16_r16_effect_step 0x1008a8 0 (.sib 4 none 0 (.d32 0xb5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1008b0 [0x0F, 0xB6, 0x44, 0x24, 0x0E] (LoadPre 0x1008b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1008b0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1008b0 5 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x1008b0 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x1008b0 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1008b5 [0x88, 0x84, 0x24, 0xB7, 0x00, 0x00, 0x00] (StorePre 0x1008b5 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x1008b5 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1008b5 7 0 (.sib 4 none 0 (.d32 0xb7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1008b5 7 0 (.sib 4 none 0 (.d32 0xb7))).toInstrSpec (mov_m8_r8_effect_step 0x1008b5 0 (by decide) (.sib 4 none 0 (.d32 0xb7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1008bc [0x48, 0x8D, 0x7C, 0x24, 0x10] (fun s => s.RIP = 0x1008bc) (leaR64Effect 0x1008bc 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1008bc 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x1008bc 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1008c1 [0xBA, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1008c1) (movR32Imm32Effect 0x1008c1 5 2 0x1)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1008c1 5 2 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1008c1 0xba (by decide) 0x1) pre_rip
  have f9 : InstrSpec 0x1008c6 [0xE8, 0x05, 0x6E, 0x02, 0x00] (PushPre 0x1008c6 5) (callEffect (fun _ => 0x1276d0) 0x1008cb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1008c6 0x1276d0 0x1008cb).toInstrSpec (call_rel32_effect_step 0x1008c6 0x26e05 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100894) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10089c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008a3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008a8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008b0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008b5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008bc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008c1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (1, 1), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008c6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 59), (1, 1), (2, 64), (3, 3), (4, 66), (5, 5), (6, 6), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1276d0) f9 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l10088c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10088c :=
  Rest.liftedBlock (rest_l10088c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10088c x hx)

theorem rest_l1008cb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1008cb bytes_l1008cb) (entryMap (live .l1008cb))
      3 0x1008cb bytes_l1008cb b_l1008cb := by
  have f0 : InstrSpec 0x1008cb [0x8B, 0x44, 0x24, 0x10] (LoadPre 0x1008cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1008cb + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1008cb 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1008cb 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x1008cb 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1008cf [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1008cf) (cmpR32Imm8Effect 0x1008cf 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1008cf 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1008cf 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008cf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008d2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1008d2 5 0xa9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1008cb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1008cb :=
  Rest.liftedBlock (rest_l1008cb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1008cb x hx)

theorem rest_l1008d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1008d8 bytes_l1008d8) (entryMap (live .l1008d8))
      4 0x1008d8 bytes_l1008d8 b_l1008d8 := by
  have f0 : InstrSpec 0x1008d8 [0x48, 0x8D, 0x7C, 0x24, 0x48] (fun s => s.RIP = 0x1008d8) (leaR64Effect 0x1008d8 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1008d8 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x1008d8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1008dd [0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1008dd) (leaR64Effect 0x1008dd 2 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1008dd 2 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (lea_r64_effect_step 0x1008dd 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1008e5 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x1008e5) (movR64R64Effect 0x1008e5 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1008e5 6 14).toInstrSpec (mov_r64_r64_effect_step 0x1008e5 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1008e8 [0xE8, 0xC3, 0x2F, 0x00, 0x00] (PushPre 0x1008e8 5) (callEffect (fun _ => 0x1038b0) 0x1008ed)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1008e8 0x1038b0 0x1008ed).toInstrSpec (call_rel32_effect_step 0x1008e8 0x2fc3 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008e5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008e8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1038b0) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l1008d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1008d8 :=
  Rest.liftedBlock (rest_l1008d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1008d8 x hx)

theorem rest_l1008ed [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1008ed bytes_l1008ed) (entryMap (live .l1008ed))
      3 0x1008ed bytes_l1008ed b_l1008ed := by
  have f0 : InstrSpec 0x1008ed [0x8B, 0x44, 0x24, 0x48] (LoadPre 0x1008ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1008ed + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1008ed 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1008ed 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r32_m32_low_effect_step 0x1008ed 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1008f1 [0x83, 0xF8, 0x02] (fun s => s.RIP = 0x1008f1) (cmpR32Imm8Effect 0x1008f1 3 0 0x2)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1008f1 3 0 0x2).toInstrSpec (cmp_r32_imm8_effect_step 0x1008f1 0xf8 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008f1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008f4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x1008f4 5 0xcd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1008ed [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1008ed :=
  Rest.liftedBlock (rest_l1008ed code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1008ed x hx)

theorem rest_l1008fa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1008fa bytes_l1008fa) (entryMap (live .l1008fa))
      8 0x1008fa bytes_l1008fa b_l1008fa := by
  have f0 : InstrSpec 0x1008fa [0x48, 0x8B, 0x44, 0x24, 0x50] (LoadPre 0x1008fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1008fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1008fa 0 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1008fa 0 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1008fa 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1008ff [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x1008ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1008ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1008ff 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1008ff 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1008ff 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x100904 [0x4C, 0x89, 0x7B, 0x08] (StorePre 0x100904 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100904 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100904 15 (.base 3 (.d8 0x8)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100904 15 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x100904 0x4c (by decide) 7 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100908 [0x4C, 0x89, 0x63, 0x10] (StorePre 0x100908 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x100908 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100908 12 (.base 3 (.d8 0x10)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100908 12 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x100908 0x4c (by decide) 4 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10090c [0x48, 0x89, 0x43, 0x18] (StorePre 0x10090c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10090c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10090c 0 (.base 3 (.d8 0x18)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x10090c 0 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10090c 0x48 (by decide) 0 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x100910 [0x48, 0x89, 0x4B, 0x20] (StorePre 0x100910 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x100910 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100910 1 (.base 3 (.d8 0x20)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100910 1 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x100910 0x48 (by decide) 1 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x100914 [0xC7, 0x03, 0x02, 0x00, 0x00, 0x00] (StorePre 0x100914 6 (fun s => AddrMode.addr (.base 3 .none) s (0x100914 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x100914 6 (.base 3 .none) 0x2)
      [.gpr 3] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x100914 6 (.base 3 .none) 0x2).toInstrSpec (mov_m32_imm32_effect_step 0x100914 (.base 3 .none) (by decide) (by decide) (by decide) 0x2) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1008ff) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100904) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100908) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10090c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100910) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100914) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10091a) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 62) (jmp_rel32_effect_step 0x10091a 0xe7 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1008fa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1008fa :=
  Rest.liftedBlock (rest_l1008fa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1008fa x hx)

theorem rest_l10091f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10091f bytes_l10091f) (entryMap (live .l10091f))
      18 0x10091f bytes_l10091f b_l10091f := by
  have f0 : InstrSpec 0x10091f [0x8B, 0xBC, 0x24, 0xA3, 0x00, 0x00, 0x00] (LoadPre 0x10091f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x10091f + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10091f 7 (.sib 4 none 0 (.d32 0xa3)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x10091f 7 (.sib 4 none 0 (.d32 0xa3))).toInstrSpec (mov_r32_m32_low_effect_step 0x10091f 7 (.sib 4 none 0 (.d32 0xa3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100926 [0x89, 0x7C, 0x24, 0x7C] (StorePre 0x100926 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x100926 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100926 7 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x100926 7 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m32_r32_low_effect_step 0x100926 7 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10092a [0x48, 0x8B, 0xBC, 0x24, 0x9B, 0x00, 0x00, 0x00] (LoadPre 0x10092a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9b)) s (0x10092a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10092a 7 (.sib 4 none 0 (.d32 0x9b)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x10092a 7 (.sib 4 none 0 (.d32 0x9b))).toInstrSpec (mov_r64_m64_effect_step 0x10092a 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x9b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x100932 [0x48, 0x89, 0x7C, 0x24, 0x74] (StorePre 0x100932 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x100932 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100932 7 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100932 7 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m64_r64_effect_step 0x100932 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x100937 [0x48, 0x8B, 0xBC, 0x24, 0x93, 0x00, 0x00, 0x00] (LoadPre 0x100937 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x93)) s (0x100937 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100937 7 (.sib 4 none 0 (.d32 0x93)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100937 7 (.sib 4 none 0 (.d32 0x93))).toInstrSpec (mov_r64_m64_effect_step 0x100937 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x93)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10093f [0x48, 0x89, 0x7C, 0x24, 0x6C] (StorePre 0x10093f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x10093f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10093f 7 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10093f 7 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m64_r64_effect_step 0x10093f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x100944 [0x48, 0x8B, 0xBC, 0x24, 0x83, 0x00, 0x00, 0x00] (LoadPre 0x100944 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x83)) s (0x100944 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100944 7 (.sib 4 none 0 (.d32 0x83)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x100944 7 (.sib 4 none 0 (.d32 0x83))).toInstrSpec (mov_r64_m64_effect_step 0x100944 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x83)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10094c [0x4C, 0x8B, 0x8C, 0x24, 0x8B, 0x00, 0x00, 0x00] (LoadPre 0x10094c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8b)) s (0x10094c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10094c 9 (.sib 4 none 0 (.d32 0x8b)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR64M64Effect_footprint 0x10094c 9 (.sib 4 none 0 (.d32 0x8b))).toInstrSpec (mov_r64_m64_effect_step 0x10094c 0x4c (by decide) 1 (.sib 4 none 0 (.d32 0x8b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x100954 [0x4C, 0x89, 0x4C, 0x24, 0x64] (StorePre 0x100954 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x100954 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100954 9 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100954 9 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m64_r64_effect_step 0x100954 0x4c (by decide) 1 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x100959 [0x48, 0x89, 0x7C, 0x24, 0x5C] (StorePre 0x100959 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x100959 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100959 7 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100959 7 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m64_r64_effect_step 0x100959 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10095e [0x48, 0x89, 0x74, 0x24, 0x4C] (StorePre 0x10095e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10095e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10095e 6 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10095e 6 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_m64_r64_effect_step 0x10095e 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x100963 [0x44, 0x89, 0x44, 0x24, 0x54] (StorePre 0x100963 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x100963 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100963 8 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x100963 8 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_m32_r32_effect_step 0x100963 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x100968 [0x88, 0x54, 0x24, 0x58] (StorePre 0x100968 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100968 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100968 4 2 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x100968 4 2 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m8_r8_effect_step 0x100968 2 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10096c [0x0F, 0xB7, 0x54, 0x24, 0x0C] (LoadPre 0x10096c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10096c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10096c 5 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x10096c 5 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x10096c 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x100971 [0x66, 0x89, 0x54, 0x24, 0x59] (StorePre 0x100971 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x100971 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100971 5 2 (.sib 4 none 0 (.d8 0x59)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x100971 5 2 (.sib 4 none 0 (.d8 0x59))).toInstrSpec (mov_m16_r16_effect_step 0x100971 2 (.sib 4 none 0 (.d8 0x59)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x100976 [0x0F, 0xB6, 0x54, 0x24, 0x0E] (LoadPre 0x100976 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x100976 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100976 5 2 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x100976 5 2 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x100976 2 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10097b [0x88, 0x54, 0x24, 0x5B] (StorePre 0x10097b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x10097b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10097b 4 2 (.sib 4 none 0 (.d8 0x5b)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x10097b 4 2 (.sib 4 none 0 (.d8 0x5b))).toInstrSpec (mov_m8_r8_effect_step 0x10097b 2 (by decide) (.sib 4 none 0 (.d8 0x5b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100926) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10092a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 56), (8, 8), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100932) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 56), (8, 8), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100937) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 59), (8, 8), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10093f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 59), (8, 8), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100944) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10094c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100954) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100959) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10095e) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100963) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100968) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10096c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 71), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100971) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 71), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100976) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 74), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10097b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 74), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10097f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 77) (jmp_rel8_effect_step 0x10097f 0x4a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l10091f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10091f :=
  Rest.liftedBlock (rest_l10091f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10091f x hx)

theorem rest_l100981 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100981 bytes_l100981) (entryMap (live .l100981))
      15 0x100981 bytes_l100981 b_l100981 := by
  have f0 : InstrSpec 0x100981 [0x48, 0x8B, 0x4C, 0x24, 0x14] (LoadPre 0x100981 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100981 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100981 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x100981 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r64_m64_effect_step 0x100981 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x100986 [0x48, 0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x100986 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100986 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100986 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100986 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r64_m64_effect_step 0x100986 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10098b [0x48, 0x89, 0x54, 0x24, 0x54] (StorePre 0x10098b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x10098b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10098b 2 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10098b 2 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (mov_m64_r64_effect_step 0x10098b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x100990 [0x48, 0x8B, 0x54, 0x24, 0x24] (LoadPre 0x100990 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100990 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100990 2 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x100990 2 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r64_m64_effect_step 0x100990 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x100995 [0x48, 0x89, 0x54, 0x24, 0x5C] (StorePre 0x100995 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x100995 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100995 2 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x100995 2 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m64_r64_effect_step 0x100995 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10099a [0x48, 0x8B, 0x54, 0x24, 0x2C] (LoadPre 0x10099a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x10099a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10099a 2 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x10099a 2 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_r64_m64_effect_step 0x10099a 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x10099f [0x48, 0x89, 0x54, 0x24, 0x64] (StorePre 0x10099f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x10099f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10099f 2 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10099f 2 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m64_r64_effect_step 0x10099f 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1009a4 [0x48, 0x8B, 0x54, 0x24, 0x34] (LoadPre 0x1009a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1009a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009a4 2 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1009a4 2 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r64_m64_effect_step 0x1009a4 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1009a9 [0x48, 0x89, 0x54, 0x24, 0x6C] (StorePre 0x1009a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1009a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1009a9 2 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1009a9 2 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m64_r64_effect_step 0x1009a9 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1009ae [0x48, 0x8B, 0x54, 0x24, 0x3C] (LoadPre 0x1009ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1009ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009ae 2 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1009ae 2 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r64_m64_effect_step 0x1009ae 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1009b3 [0x48, 0x89, 0x54, 0x24, 0x74] (StorePre 0x1009b3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x1009b3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1009b3 2 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1009b3 2 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m64_r64_effect_step 0x1009b3 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1009b8 [0x8B, 0x54, 0x24, 0x44] (LoadPre 0x1009b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1009b8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1009b8 2 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1009b8 2 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_r32_m32_low_effect_step 0x1009b8 2 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1009bc [0x89, 0x54, 0x24, 0x7C] (StorePre 0x1009bc 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1009bc + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1009bc 2 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1009bc 2 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m32_r32_low_effect_step 0x1009bc 2 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1009c0 [0x48, 0x89, 0x4C, 0x24, 0x4C] (StorePre 0x1009c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1009c0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1009c0 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1009c0 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_m64_r64_effect_step 0x1009c0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100986) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10098b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100990) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100995) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 58), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10099a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10099f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 53), (2, 61), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009a4) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009a9) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 53), (2, 64), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009ae) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009b3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 53), (2, 67), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009b8) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009bc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009c0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009c5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 74) (jmp_rel8_effect_step 0x1009c5 0x4 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l100981 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100981 :=
  Rest.liftedBlock (rest_l100981 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100981 x hx)

theorem rest_l1009c7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1009c7 bytes_l1009c7) (entryMap (live .l1009c7))
      1 0x1009c7 bytes_l1009c7 b_l1009c7 := by
  have f0 : InstrSpec 0x1009c7 [0x8B, 0x4C, 0x24, 0x4C] (LoadPre 0x1009c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1009c7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1009c7 1 (.sib 4 none 0 (.d8 0x4c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1009c7 1 (.sib 4 none 0 (.d8 0x4c))).toInstrSpec (mov_r32_m32_low_effect_step 0x1009c7 1 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009cb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1009c7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1009c7 :=
  Rest.liftedBlock (rest_l1009c7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1009c7 x hx)

theorem rest_l1009cb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1009cb bytes_l1009cb) (entryMap (live .l1009cb))
      14 0x1009cb bytes_l1009cb b_l1009cb := by
  have f0 : InstrSpec 0x1009cb [0x48, 0x8B, 0x54, 0x24, 0x50] (LoadPre 0x1009cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1009cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009cb 2 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x1009cb 2 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x1009cb 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1009d0 [0x48, 0x8B, 0x74, 0x24, 0x58] (LoadPre 0x1009d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1009d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009d0 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x1009d0 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x1009d0 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1009d5 [0x48, 0x8B, 0x7C, 0x24, 0x78] (LoadPre 0x1009d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1009d5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009d5 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1009d5 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x1009d5 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1009da [0x48, 0x89, 0x7B, 0x30] (StorePre 0x1009da 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1009da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009da 7 (.base 3 (.d8 0x30)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1009da 7 (.base 3 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1009da 0x48 (by decide) 7 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1009de [0x48, 0x8B, 0x7C, 0x24, 0x70] (LoadPre 0x1009de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1009de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009de 7 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1009de 7 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x1009de 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1009e3 [0x48, 0x89, 0x7B, 0x28] (StorePre 0x1009e3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1009e3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009e3 7 (.base 3 (.d8 0x28)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1009e3 7 (.base 3 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x1009e3 0x48 (by decide) 7 (.base 3 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1009e7 [0x48, 0x8B, 0x7C, 0x24, 0x68] (LoadPre 0x1009e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1009e7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009e7 7 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1009e7 7 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x1009e7 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1009ec [0x48, 0x89, 0x7B, 0x20] (StorePre 0x1009ec 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1009ec + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009ec 7 (.base 3 (.d8 0x20)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1009ec 7 (.base 3 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x1009ec 0x48 (by decide) 7 (.base 3 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1009f0 [0x48, 0x8B, 0x7C, 0x24, 0x60] (LoadPre 0x1009f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1009f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009f0 7 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1009f0 7 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x1009f0 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1009f5 [0x48, 0x89, 0x7B, 0x18] (StorePre 0x1009f5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1009f5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009f5 7 (.base 3 (.d8 0x18)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1009f5 7 (.base 3 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x1009f5 0x48 (by decide) 7 (.base 3 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1009f9 [0x89, 0x03] (StorePre 0x1009f9 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1009f9 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1009f9 0 (.base 3 .none))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1009f9 0 (.base 3 .none)).toInstrSpec (mov_m32_r32_low_effect_step 0x1009f9 0 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1009fb [0x89, 0x4B, 0x04] (StorePre 0x1009fb 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1009fb + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1009fb 1 (.base 3 (.d8 0x4)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1009fb 1 (.base 3 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1009fb 1 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1009fe [0x48, 0x89, 0x53, 0x08] (StorePre 0x1009fe 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1009fe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009fe 2 (.base 3 (.d8 0x8)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x1009fe 2 (.base 3 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x1009fe 0x48 (by decide) 2 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x100a02 [0x48, 0x89, 0x73, 0x10] (StorePre 0x100a02 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x100a02 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100a02 6 (.base 3 (.d8 0x10)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x100a02 6 (.base 3 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x100a02 0x48 (by decide) 6 (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009d0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009d5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009da) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009de) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009e3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009e7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009ec) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009f0) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009f5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009f9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009fb) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1009fe) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a02) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a06) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 73) (by decide) rfl

theorem block_l1009cb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1009cb :=
  Rest.liftedBlock (rest_l1009cb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1009cb x hx)

theorem rest_l100a06 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x100a06 bytes_l100a06) (entryMap (live .l100a06))
      9 0x100a06 bytes_l100a06 b_l100a06 := by
  have f0 : InstrSpec 0x100a06 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x100a06) (movR64R64Effect 0x100a06 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x100a06 0 3).toInstrSpec (mov_r64_r64_effect_step 0x100a06 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x100a09 [0x48, 0x81, 0xC4, 0xB8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x100a09) (addR64Imm32Effect 0x100a09 4 0xb8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x100a09 4 0xb8).toInstrSpec (add_r64_imm32_effect_step 0x100a09 0x48 0xc4 0xb8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x100a10 [0x5B] (PopPre 0x100a10) (popR64Effect 0x100a10 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100a10 1 3).toInstrSpec (pop_r64_effect_step 0x100a10 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x100a11 [0x41, 0x5C] (PopPre 0x100a11) (popR64Effect 0x100a11 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100a11 2 12).toInstrSpec (pop_r64_rex_effect_step 0x100a11 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x100a13 [0x41, 0x5D] (PopPre 0x100a13) (popR64Effect 0x100a13 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100a13 2 13).toInstrSpec (pop_r64_rex_effect_step 0x100a13 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x100a15 [0x41, 0x5E] (PopPre 0x100a15) (popR64Effect 0x100a15 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100a15 2 14).toInstrSpec (pop_r64_rex_effect_step 0x100a15 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x100a17 [0x41, 0x5F] (PopPre 0x100a17) (popR64Effect 0x100a17 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100a17 2 15).toInstrSpec (pop_r64_rex_effect_step 0x100a17 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x100a19 [0x5D] (PopPre 0x100a19) (popR64Effect 0x100a19 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x100a19 1 5).toInstrSpec (pop_r64_effect_step 0x100a19 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x100a1a [0xC3] (RetPre 0x100a1a) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x100a1a).toInstrSpec (ret_effect_step 0x100a1a) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a09) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a10) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a11) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a13) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a15) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a17) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a19) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100a1a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l100a06 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l100a06 :=
  Rest.liftedBlock (rest_l100a06 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l100a06 x hx)

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

theorem_by block_l100510_eval :
    program.runBlock (dialect code) ⟨.l100510, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100531_eval :
    program.runBlock (dialect code) ⟨.l100531, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100544_eval :
    program.runBlock (dialect code) ⟨.l100544, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100551_eval :
    program.runBlock (dialect code) ⟨.l100551, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100562_eval :
    program.runBlock (dialect code) ⟨.l100562, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100582_eval :
    program.runBlock (dialect code) ⟨.l100582, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1005e6_eval :
    program.runBlock (dialect code) ⟨.l1005e6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1005f0_eval :
    program.runBlock (dialect code) ⟨.l1005f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100602_eval :
    program.runBlock (dialect code) ⟨.l100602, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100607_eval :
    program.runBlock (dialect code) ⟨.l100607, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100666_eval :
    program.runBlock (dialect code) ⟨.l100666, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10069c_eval :
    program.runBlock (dialect code) ⟨.l10069c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1006db_eval :
    program.runBlock (dialect code) ⟨.l1006db, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1006e8_eval :
    program.runBlock (dialect code) ⟨.l1006e8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1006fd_eval :
    program.runBlock (dialect code) ⟨.l1006fd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10070a_eval :
    program.runBlock (dialect code) ⟨.l10070a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100721_eval :
    program.runBlock (dialect code) ⟨.l100721, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100734_eval :
    program.runBlock (dialect code) ⟨.l100734, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100741_eval :
    program.runBlock (dialect code) ⟨.l100741, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100752_eval :
    program.runBlock (dialect code) ⟨.l100752, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100772_eval :
    program.runBlock (dialect code) ⟨.l100772, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1007d6_eval :
    program.runBlock (dialect code) ⟨.l1007d6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1007e0_eval :
    program.runBlock (dialect code) ⟨.l1007e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1007f2_eval :
    program.runBlock (dialect code) ⟨.l1007f2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1007f7_eval :
    program.runBlock (dialect code) ⟨.l1007f7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100856_eval :
    program.runBlock (dialect code) ⟨.l100856, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10088c_eval :
    program.runBlock (dialect code) ⟨.l10088c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1008cb_eval :
    program.runBlock (dialect code) ⟨.l1008cb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1008d8_eval :
    program.runBlock (dialect code) ⟨.l1008d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1008ed_eval :
    program.runBlock (dialect code) ⟨.l1008ed, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1008fa_eval :
    program.runBlock (dialect code) ⟨.l1008fa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10091f_eval :
    program.runBlock (dialect code) ⟨.l10091f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100981_eval :
    program.runBlock (dialect code) ⟨.l100981, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1009c7_eval :
    program.runBlock (dialect code) ⟨.l1009c7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1009cb_eval :
    program.runBlock (dialect code) ⟨.l1009cb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l100a06_eval :
    program.runBlock (dialect code) ⟨.l100a06, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
