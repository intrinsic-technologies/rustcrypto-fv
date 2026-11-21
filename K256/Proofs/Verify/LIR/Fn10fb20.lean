import K256.Proofs.Generate.LIR.CallPre
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem rest_l10fb20_1 [Bindings] (code : CodeMap) :
    Rest (n := 90) code lifted (codeRange 0x10fb20 bytes_l10fb20) [(1, 1), (2, 86), (3, 84), (4, 71), (5, 80), (6, 6), (7, 88), (9, 9), (10, 10), (11, 11), (12, 77), (13, 82), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x10fb7b bytes_l10fb20_1 b_l10fb20_1 := by
  have f20 : InstrSpec 0x10fb7b [0x31, 0xF6] (fun s => s.RIP = 0x10fb7b) (xorR32R32Effect 0x10fb7b 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10fb7b 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10fb7b 0xf6 (by decide)) pre_rip
  have f21 : InstrSpec 0x10fb7d [0xFF, 0xD3] (GoesTo (CallPre 0x10fb7d 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb7f) 0x12a700) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb7f)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fb7d 3 0x10fb7f).toInstrSpec (call_r64_effect_step 0x10fb7d 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(1, 1), (2, 86), (3, 84), (4, 71), (5, 80), (6, 90), (7, 88), (9, 9), (10, 10), (11, 11), (12, 77), (13, 82), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb7d) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(1, 1), (2, 86), (3, 84), (4, 92), (5, 80), (6, 90), (7, 88), (9, 9), (10, 10), (11, 11), (12, 77), (13, 82), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f21 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 94) (by decide) (by decide) rfl rfl

theorem rest_l10fb20 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fb20 bytes_l10fb20) (entryMap (live .l10fb20))
      22 0x10fb20 bytes_l10fb20 b_l10fb20 := by
  have f0 : InstrSpec 0x10fb20 [0x55] (PushPre 0x10fb20 1) (pushR64Effect 0x10fb20 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fb20 1 5).toInstrSpec (push_r64_effect_step 0x10fb20 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x10fb21 [0x41, 0x57] (PushPre 0x10fb21 2) (pushR64Effect 0x10fb21 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fb21 2 15).toInstrSpec (push_r64_rex_effect_step 0x10fb21 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x10fb23 [0x41, 0x56] (PushPre 0x10fb23 2) (pushR64Effect 0x10fb23 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fb23 2 14).toInstrSpec (push_r64_rex_effect_step 0x10fb23 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10fb25 [0x41, 0x55] (PushPre 0x10fb25 2) (pushR64Effect 0x10fb25 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fb25 2 13).toInstrSpec (push_r64_rex_effect_step 0x10fb25 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10fb27 [0x41, 0x54] (PushPre 0x10fb27 2) (pushR64Effect 0x10fb27 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fb27 2 12).toInstrSpec (push_r64_rex_effect_step 0x10fb27 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10fb29 [0x53] (PushPre 0x10fb29 1) (pushR64Effect 0x10fb29 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x10fb29 1 3).toInstrSpec (push_r64_effect_step 0x10fb29 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10fb2a [0x48, 0x81, 0xEC, 0x00, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x10fb2a) (subR64Imm32Effect 0x10fb2a 4 0x1000)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10fb2a 4 0x1000).toInstrSpec (sub_r64_imm32_effect_step 0x10fb2a 0x48 0xec 0x1000 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10fb31 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fb31 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fb31 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fb31 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fb31 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fb31 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10fb39 [0x48, 0x81, 0xEC, 0x00, 0x10, 0x00, 0x00] (fun s => s.RIP = 0x10fb39) (subR64Imm32Effect 0x10fb39 4 0x1000)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10fb39 4 0x1000).toInstrSpec (sub_r64_imm32_effect_step 0x10fb39 0x48 0xec 0x1000 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10fb40 [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fb40 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fb40 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10fb40 (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fb40 (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fb40 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10fb48 [0x48, 0x81, 0xEC, 0xA8, 0x08, 0x00, 0x00] (fun s => s.RIP = 0x10fb48) (subR64Imm32Effect 0x10fb48 4 0x8a8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10fb48 4 0x8a8).toInstrSpec (sub_r64_imm32_effect_step 0x10fb48 0x48 0xec 0x8a8 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10fb4f [0x49, 0x89, 0xCF] (fun s => s.RIP = 0x10fb4f) (movR64R64Effect 0x10fb4f 15 1)
      [.gpr 1] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x10fb4f 15 1).toInstrSpec (mov_r64_r64_effect_step 0x10fb4f 0x49 0xcf (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10fb52 [0x49, 0x89, 0xD6] (fun s => s.RIP = 0x10fb52) (movR64R64Effect 0x10fb52 14 2)
      [.gpr 2] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10fb52 14 2).toInstrSpec (mov_r64_r64_effect_step 0x10fb52 0x49 0xd6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10fb55 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x10fb55) (movR64R64Effect 0x10fb55 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x10fb55 12 6).toInstrSpec (mov_r64_r64_effect_step 0x10fb55 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10fb58 [0x48, 0x89, 0x3C, 0x24] (StorePre 0x10fb58 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fb58 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fb58 7 (.sib 4 none 0 .none))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fb58 7 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x10fb58 0x48 (by decide) 7 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10fb5c [0x48, 0x8D, 0xAC, 0x24, 0x38, 0x03, 0x00, 0x00] (fun s => s.RIP = 0x10fb5c) (leaR64Effect 0x10fb5c 5 (.sib 4 none 0 (.d32 0x338)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x10fb5c 5 (.sib 4 none 0 (.d32 0x338))).toInstrSpec (lea_r64_effect_step 0x10fb5c 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x338)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10fb64 [0x4C, 0x8D, 0xAC, 0x24, 0x28, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10fb64) (leaR64Effect 0x10fb64 13 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10fb64 13 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (lea_r64_effect_step 0x10fb64 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10fb6c [0x48, 0x8D, 0x1D, 0x8D, 0xAB, 0x01, 0x00] (fun s => s.RIP = 0x10fb6c) (leaR64Effect 0x10fb6c 3 (.rip 0x1ab8d))
      [] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x10fb6c 3 (.rip 0x1ab8d)).toInstrSpec (lea_r64_effect_step 0x10fb6c 0x48 (by decide) 3 (.rip 0x1ab8d) (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10fb73 [0xBA, 0x09, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10fb73) (movR32Imm32Effect 0x10fb73 5 2 0x109)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fb73 5 2 0x109).toInstrSpec (mov_r32_imm32_effect_step 0x10fb73 0xba (by decide) 0x109) pre_rip
  have f19 : InstrSpec 0x10fb78 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x10fb78) (movR64R64Effect 0x10fb78 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10fb78 7 13).toInstrSpec (mov_r64_r64_effect_step 0x10fb78 0x4c 0xef (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb21) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb23) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb25) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb27) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb29) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb2a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb31) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb39) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 68), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb40) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 68), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb48) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 71), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb4f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 71), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb52) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 71), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb55) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 71), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 77), (13, 13), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb58) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 71), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 77), (13, 13), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb5c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 71), (5, 80), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 77), (13, 13), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb64) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 71), (5, 80), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 77), (13, 82), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb6c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(1, 1), (2, 2), (3, 84), (4, 71), (5, 80), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 77), (13, 82), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb73) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(1, 1), (2, 86), (3, 84), (4, 71), (5, 80), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 77), (13, 82), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb78) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(1, 1), (2, 86), (3, 84), (4, 71), (5, 80), (6, 6), (7, 88), (9, 9), (10, 10), (11, 11), (12, 77), (13, 82), (14, 75), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb7b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10fb20_1 code

theorem block_l10fb20 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fb20 :=
  Rest.liftedBlock (rest_l10fb20 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fb20 x hx)

theorem rest_l10fb7f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fb7f bytes_l10fb7f) (entryMap (live .l10fb7f))
      4 0x10fb7f bytes_l10fb7f b_l10fb7f := by
  have f0 : InstrSpec 0x10fb7f [0xBA, 0x09, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10fb7f) (movR32Imm32Effect 0x10fb7f 5 2 0x109)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fb7f 5 2 0x109).toInstrSpec (mov_r32_imm32_effect_step 0x10fb7f 0xba (by decide) 0x109) pre_rip
  have f1 : InstrSpec 0x10fb84 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x10fb84) (movR64R64Effect 0x10fb84 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10fb84 7 5).toInstrSpec (mov_r64_r64_effect_step 0x10fb84 0x48 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10fb87 [0x31, 0xF6] (fun s => s.RIP = 0x10fb87) (xorR32R32Effect 0x10fb87 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10fb87 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10fb87 0xf6 (by decide)) pre_rip
  have f3 : InstrSpec 0x10fb89 [0xFF, 0xD3] (GoesTo (CallPre 0x10fb89 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb8b) 0x12a700) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fb8b)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fb89 3 0x10fb8b).toInstrSpec (call_r64_effect_step 0x10fb89 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb84) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb87) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb89) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10fb7f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fb7f :=
  Rest.liftedBlock (rest_l10fb7f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fb7f x hx)

theorem rest_l10fb8b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fb8b bytes_l10fb8b) (entryMap (live .l10fb8b))
      6 0x10fb8b bytes_l10fb8b b_l10fb8b := by
  have f0 : InstrSpec 0x10fb8b [0x48, 0x8D, 0xAC, 0x24, 0x68, 0x15, 0x00, 0x00] (fun s => s.RIP = 0x10fb8b) (leaR64Effect 0x10fb8b 5 (.sib 4 none 0 (.d32 0x1568)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x10fb8b 5 (.sib 4 none 0 (.d32 0x1568))).toInstrSpec (lea_r64_effect_step 0x10fb8b 0x48 (by decide) 5 (.sib 4 none 0 (.d32 0x1568)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fb93 [0x48, 0xC7, 0xC7, 0xC8, 0x2B, 0x20, 0x00] (fun s => s.RIP = 0x10fb93) (movR64Imm32Effect 0x10fb93 7 0x202bc8)
      [] [] [.reg 7, .rip] :=
    (movR64Imm32Effect_footprint 0x10fb93 7 0x202bc8).toInstrSpec (mov_r64_imm32_effect_step 0x10fb93 0x48 0xc7 (by decide) (by decide) (by decide) 0x202bc8) pre_rip
  have f2 : InstrSpec 0x10fb9a [0x4C, 0x89, 0xE6] (fun s => s.RIP = 0x10fb9a) (movR64R64Effect 0x10fb9a 6 12)
      [.gpr 12] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10fb9a 6 12).toInstrSpec (mov_r64_r64_effect_step 0x10fb9a 0x4c 0xe6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10fb9d [0x48, 0x89, 0xEA] (fun s => s.RIP = 0x10fb9d) (movR64R64Effect 0x10fb9d 2 5)
      [.gpr 5] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10fb9d 2 5).toInstrSpec (mov_r64_r64_effect_step 0x10fb9d 0x48 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10fba0 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x10fba0) (movR64R64Effect 0x10fba0 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10fba0 1 13).toInstrSpec (mov_r64_r64_effect_step 0x10fba0 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10fba3 [0xE8, 0xA8, 0xF5, 0xFF, 0xFF] (PushPre 0x10fba3 5) (callEffect (fun _ => 0x10f150) 0x10fba8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10fba3 0x10f150 0x10fba8).toInstrSpec (call_rel32_effect_step 0x10fba3 0xfffff5a8 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb93) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb9a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fb9d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fba0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 59), (3, 3), (4, 4), (5, 53), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fba3) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 59), (3, 3), (4, 63), (5, 53), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f150) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l10fb8b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fb8b :=
  Rest.liftedBlock (rest_l10fb8b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fb8b x hx)

theorem rest_l10fba8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fba8 bytes_l10fba8) (entryMap (live .l10fba8))
      5 0x10fba8 bytes_l10fba8 b_l10fba8 := by
  have f0 : InstrSpec 0x10fba8 [0x48, 0x8D, 0xBC, 0x24, 0xC8, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x10fba8) (leaR64Effect 0x10fba8 7 (.sib 4 none 0 (.d32 0xbc8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10fba8 7 (.sib 4 none 0 (.d32 0xbc8))).toInstrSpec (lea_r64_effect_step 0x10fba8 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xbc8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fbb0 [0x4C, 0x8D, 0x25, 0x69, 0xAC, 0x01, 0x00] (fun s => s.RIP = 0x10fbb0) (leaR64Effect 0x10fbb0 12 (.rip 0x1ac69))
      [] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x10fbb0 12 (.rip 0x1ac69)).toInstrSpec (lea_r64_effect_step 0x10fbb0 0x4c (by decide) 4 (.rip 0x1ac69) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10fbb7 [0xBA, 0x80, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x10fbb7) (movR32Imm32Effect 0x10fbb7 5 2 0x780)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fbb7 5 2 0x780).toInstrSpec (mov_r32_imm32_effect_step 0x10fbb7 0xba (by decide) 0x780) pre_rip
  have f3 : InstrSpec 0x10fbbc [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x10fbbc) (movR64R64Effect 0x10fbbc 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10fbbc 6 5).toInstrSpec (mov_r64_r64_effect_step 0x10fbbc 0x48 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10fbbf [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x10fbbf 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbc2) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbc2)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fbbf 12 0x10fbc2).toInstrSpec (call_r64_rex_effect_step 0x10fbbf 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbb0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbb7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbbc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 5), (6, 59), (7, 53), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbbf) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 3), (4, 61), (5, 5), (6, 59), (7, 53), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10fba8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fba8 :=
  Rest.liftedBlock (rest_l10fba8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fba8 x hx)

theorem rest_l10fbc2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fbc2 bytes_l10fbc2) (entryMap (live .l10fbc2))
      4 0x10fbc2 bytes_l10fbc2 b_l10fbc2 := by
  have f0 : InstrSpec 0x10fbc2 [0x48, 0x8D, 0xBC, 0x24, 0x48, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10fbc2) (leaR64Effect 0x10fbc2 7 (.sib 4 none 0 (.d32 0x1348)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10fbc2 7 (.sib 4 none 0 (.d32 0x1348))).toInstrSpec (lea_r64_effect_step 0x10fbc2 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1348)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fbca [0xBA, 0x20, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10fbca) (movR32Imm32Effect 0x10fbca 5 2 0x220)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fbca 5 2 0x220).toInstrSpec (mov_r32_imm32_effect_step 0x10fbca 0xba (by decide) 0x220) pre_rip
  have f2 : InstrSpec 0x10fbcf [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10fbcf) (movR64R64Effect 0x10fbcf 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10fbcf 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10fbcf 0x4c 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10fbd2 [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x10fbd2 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbd5) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fbd5)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fbd2 12 0x10fbd5).toInstrSpec (call_r64_rex_effect_step 0x10fbd2 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbcf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbd2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10fbc2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fbc2 :=
  Rest.liftedBlock (rest_l10fbc2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fbc2 x hx)

theorem rest_l10fbd5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fbd5 bytes_l10fbd5) (entryMap (live .l10fbd5))
      6 0x10fbd5 bytes_l10fbd5 b_l10fbd5 := by
  have f0 : InstrSpec 0x10fbd5 [0x4C, 0x8D, 0xAC, 0x24, 0x18, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10fbd5) (leaR64Effect 0x10fbd5 13 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10fbd5 13 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (lea_r64_effect_step 0x10fbd5 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fbdd [0x48, 0x8D, 0x6C, 0x24, 0x08] (fun s => s.RIP = 0x10fbdd) (leaR64Effect 0x10fbdd 5 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x10fbdd 5 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10fbdd 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10fbe2 [0xBA, 0x09, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10fbe2) (movR32Imm32Effect 0x10fbe2 5 2 0x109)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fbe2 5 2 0x109).toInstrSpec (mov_r32_imm32_effect_step 0x10fbe2 0xba (by decide) 0x109) pre_rip
  have f3 : InstrSpec 0x10fbe7 [0x48, 0x89, 0xEF] (fun s => s.RIP = 0x10fbe7) (movR64R64Effect 0x10fbe7 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10fbe7 7 5).toInstrSpec (mov_r64_r64_effect_step 0x10fbe7 0x48 0xef (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10fbea [0x31, 0xF6] (fun s => s.RIP = 0x10fbea) (xorR32R32Effect 0x10fbea 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10fbea 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10fbea 0xf6 (by decide)) pre_rip
  have f5 : InstrSpec 0x10fbec [0xFF, 0xD3] (GoesTo (CallPre 0x10fbec 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbee) 0x12a700) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbee)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fbec 3 0x10fbee).toInstrSpec (call_r64_effect_step 0x10fbec 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbdd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 55), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbe2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 55), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbe7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 55), (6, 6), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbea) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (3, 3), (4, 4), (5, 55), (6, 61), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbec) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 57), (3, 3), (4, 63), (5, 55), (6, 61), (7, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f5 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l10fbd5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fbd5 :=
  Rest.liftedBlock (rest_l10fbd5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fbd5 x hx)

theorem rest_l10fbee [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fbee bytes_l10fbee) (entryMap (live .l10fbee))
      4 0x10fbee bytes_l10fbee b_l10fbee := by
  have f0 : InstrSpec 0x10fbee [0xBA, 0x09, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x10fbee) (movR32Imm32Effect 0x10fbee 5 2 0x109)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fbee 5 2 0x109).toInstrSpec (mov_r32_imm32_effect_step 0x10fbee 0xba (by decide) 0x109) pre_rip
  have f1 : InstrSpec 0x10fbf3 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x10fbf3) (movR64R64Effect 0x10fbf3 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10fbf3 7 13).toInstrSpec (mov_r64_r64_effect_step 0x10fbf3 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10fbf6 [0x31, 0xF6] (fun s => s.RIP = 0x10fbf6) (xorR32R32Effect 0x10fbf6 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10fbf6 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10fbf6 0xf6 (by decide)) pre_rip
  have f3 : InstrSpec 0x10fbf8 [0xFF, 0xD3] (GoesTo (CallPre 0x10fbf8 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbfa) 0x12a700) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x10fbfa)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fbf8 3 0x10fbfa).toInstrSpec (call_r64_effect_step 0x10fbf8 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a700
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbf3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbf6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fbf8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a700) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10fbee [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fbee :=
  Rest.liftedBlock (rest_l10fbee code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fbee x hx)

theorem rest_l10fbfa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fbfa bytes_l10fbfa) (entryMap (live .l10fbfa))
      6 0x10fbfa bytes_l10fbfa b_l10fbfa := by
  have f0 : InstrSpec 0x10fbfa [0x4C, 0x8D, 0xAC, 0x24, 0x68, 0x15, 0x00, 0x00] (fun s => s.RIP = 0x10fbfa) (leaR64Effect 0x10fbfa 13 (.sib 4 none 0 (.d32 0x1568)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x10fbfa 13 (.sib 4 none 0 (.d32 0x1568))).toInstrSpec (lea_r64_effect_step 0x10fbfa 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x1568)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fc02 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10fc02) (movR64R64Effect 0x10fc02 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10fc02 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10fc02 0x4c 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10fc05 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10fc05) (movR64R64Effect 0x10fc05 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10fc05 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10fc05 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10fc08 [0x4C, 0x89, 0xEA] (fun s => s.RIP = 0x10fc08) (movR64R64Effect 0x10fc08 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10fc08 2 13).toInstrSpec (mov_r64_r64_effect_step 0x10fc08 0x4c 0xea (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10fc0b [0x48, 0x89, 0xE9] (fun s => s.RIP = 0x10fc0b) (movR64R64Effect 0x10fc0b 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10fc0b 1 5).toInstrSpec (mov_r64_r64_effect_step 0x10fc0b 0x48 0xe9 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10fc0e [0xE8, 0x3D, 0xF5, 0xFF, 0xFF] (PushPre 0x10fc0e 5) (callEffect (fun _ => 0x10f150) 0x10fc13)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10fc0e 0x10f150 0x10fc13).toInstrSpec (call_rel32_effect_step 0x10fc0e 0xfffff53d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc02) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc08) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc0b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 61), (2, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc0e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 61), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 55), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10f150) f5 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l10fbfa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fbfa :=
  Rest.liftedBlock (rest_l10fbfa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fbfa x hx)

theorem rest_l10fc13 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fc13 bytes_l10fc13) (entryMap (live .l10fc13))
      5 0x10fc13 bytes_l10fc13 b_l10fc13 := by
  have f0 : InstrSpec 0x10fc13 [0x4C, 0x8D, 0xB4, 0x24, 0x28, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10fc13) (leaR64Effect 0x10fc13 14 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x10fc13 14 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (lea_r64_effect_step 0x10fc13 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fc1b [0xBA, 0x80, 0x07, 0x00, 0x00] (fun s => s.RIP = 0x10fc1b) (movR32Imm32Effect 0x10fc1b 5 2 0x780)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fc1b 5 2 0x780).toInstrSpec (mov_r32_imm32_effect_step 0x10fc1b 0xba (by decide) 0x780) pre_rip
  have f2 : InstrSpec 0x10fc20 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10fc20) (movR64R64Effect 0x10fc20 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10fc20 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10fc20 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10fc23 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x10fc23) (movR64R64Effect 0x10fc23 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10fc23 6 13).toInstrSpec (mov_r64_r64_effect_step 0x10fc23 0x4c 0xee (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10fc26 [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x10fc26 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc29) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc29)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fc26 12 0x10fc29).toInstrSpec (call_r64_rex_effect_step 0x10fc26 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc1b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc20) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc23) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc26) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10fc13 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fc13 :=
  Rest.liftedBlock (rest_l10fc13 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fc13 x hx)

theorem rest_l10fc29 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fc29 bytes_l10fc29) (entryMap (live .l10fc29))
      4 0x10fc29 bytes_l10fc29 b_l10fc29 := by
  have f0 : InstrSpec 0x10fc29 [0x48, 0x8D, 0xBC, 0x24, 0xA8, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x10fc29) (leaR64Effect 0x10fc29 7 (.sib 4 none 0 (.d32 0x9a8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10fc29 7 (.sib 4 none 0 (.d32 0x9a8))).toInstrSpec (lea_r64_effect_step 0x10fc29 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x9a8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fc31 [0xBA, 0x20, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10fc31) (movR32Imm32Effect 0x10fc31 5 2 0x220)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fc31 5 2 0x220).toInstrSpec (mov_r32_imm32_effect_step 0x10fc31 0xba (by decide) 0x220) pre_rip
  have f2 : InstrSpec 0x10fc36 [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x10fc36) (movR64R64Effect 0x10fc36 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10fc36 6 5).toInstrSpec (mov_r64_r64_effect_step 0x10fc36 0x48 0xee (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10fc39 [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x10fc39 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc3c) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc3c)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fc39 12 0x10fc3c).toInstrSpec (call_r64_rex_effect_step 0x10fc39 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc36) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc39) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10fc29 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fc29 :=
  Rest.liftedBlock (rest_l10fc29 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fc29 x hx)

theorem rest_l10fc3c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fc3c bytes_l10fc3c) (entryMap (live .l10fc3c))
      4 0x10fc3c bytes_l10fc3c b_l10fc3c := by
  have f0 : InstrSpec 0x10fc3c [0xBA, 0xA0, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x10fc3c) (movR32Imm32Effect 0x10fc3c 5 2 0x9a0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fc3c 5 2 0x9a0).toInstrSpec (mov_r32_imm32_effect_step 0x10fc3c 0xba (by decide) 0x9a0) pre_rip
  have f1 : InstrSpec 0x10fc41 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x10fc41) (movR64R64Effect 0x10fc41 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10fc41 7 13).toInstrSpec (mov_r64_r64_effect_step 0x10fc41 0x4c 0xef (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10fc44 [0x48, 0x8D, 0xB4, 0x24, 0xC8, 0x0B, 0x00, 0x00] (fun s => s.RIP = 0x10fc44) (leaR64Effect 0x10fc44 6 (.sib 4 none 0 (.d32 0xbc8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10fc44 6 (.sib 4 none 0 (.d32 0xbc8))).toInstrSpec (lea_r64_effect_step 0x10fc44 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xbc8)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10fc4c [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x10fc4c 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc4f) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc4f)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fc4c 12 0x10fc4f).toInstrSpec (call_r64_rex_effect_step 0x10fc4c 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc41) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc44) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc4c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 53), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10fc3c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fc3c :=
  Rest.liftedBlock (rest_l10fc3c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fc3c x hx)

theorem rest_l10fc4f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fc4f bytes_l10fc4f) (entryMap (live .l10fc4f))
      4 0x10fc4f bytes_l10fc4f b_l10fc4f := by
  have f0 : InstrSpec 0x10fc4f [0x48, 0x8D, 0xBC, 0x24, 0x08, 0x1F, 0x00, 0x00] (fun s => s.RIP = 0x10fc4f) (leaR64Effect 0x10fc4f 7 (.sib 4 none 0 (.d32 0x1f08)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x10fc4f 7 (.sib 4 none 0 (.d32 0x1f08))).toInstrSpec (lea_r64_effect_step 0x10fc4f 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0x1f08)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fc57 [0xBA, 0xA0, 0x09, 0x00, 0x00] (fun s => s.RIP = 0x10fc57) (movR32Imm32Effect 0x10fc57 5 2 0x9a0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x10fc57 5 2 0x9a0).toInstrSpec (mov_r32_imm32_effect_step 0x10fc57 0xba (by decide) 0x9a0) pre_rip
  have f2 : InstrSpec 0x10fc5c [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x10fc5c) (movR64R64Effect 0x10fc5c 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x10fc5c 6 14).toInstrSpec (mov_r64_r64_effect_step 0x10fc5c 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10fc5f [0x41, 0xFF, 0xD4] (GoesTo (CallPre 0x10fc5f 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc62) 0x12a820) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10fc62)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x10fc5f 12 0x10fc62).toInstrSpec (call_r64_rex_effect_step 0x10fc5f 0x41 0xd4 (by decide) (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 12 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x12a820
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc57) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc5c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc5f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12a820) f3 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l10fc4f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fc4f :=
  Rest.liftedBlock (rest_l10fc4f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fc4f x hx)

theorem rest_l10fc62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fc62 bytes_l10fc62) (entryMap (live .l10fc62))
      9 0x10fc62 bytes_l10fc62 b_l10fc62 := by
  have f0 : InstrSpec 0x10fc62 [0x48, 0x8D, 0x84, 0x24, 0xA8, 0x28, 0x00, 0x00] (fun s => s.RIP = 0x10fc62) (leaR64Effect 0x10fc62 0 (.sib 4 none 0 (.d32 0x28a8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x10fc62 0 (.sib 4 none 0 (.d32 0x28a8))).toInstrSpec (lea_r64_effect_step 0x10fc62 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x28a8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fc6a [0x4C, 0x89, 0xAC, 0x24, 0x28, 0x02, 0x00, 0x00] (StorePre 0x10fc6a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x228)) s (0x10fc6a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10fc6a 13 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fc6a 13 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (mov_m64_r64_effect_step 0x10fc6a 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10fc72 [0x48, 0x89, 0x84, 0x24, 0x30, 0x02, 0x00, 0x00] (StorePre 0x10fc72 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x230)) s (0x10fc72 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10fc72 0 (.sib 4 none 0 (.d32 0x230)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10fc72 0 (.sib 4 none 0 (.d32 0x230))).toInstrSpec (mov_m64_r64_effect_step 0x10fc72 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x230)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10fc7a [0x48, 0xC7, 0x84, 0x24, 0x38, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fc7a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x238)) s (0x10fc7a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10fc7a (.sib 4 none 0 (.d32 0x238)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fc7a (.sib 4 none 0 (.d32 0x238)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fc7a 0x48 (by decide) (.sib 4 none 0 (.d32 0x238)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10fc86 [0x48, 0xC7, 0x84, 0x24, 0x68, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10fc86 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x268)) s (0x10fc86 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10fc86 (.sib 4 none 0 (.d32 0x268)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10fc86 (.sib 4 none 0 (.d32 0x268)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10fc86 0x48 (by decide) (.sib 4 none 0 (.d32 0x268)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10fc92 [0x48, 0x8D, 0xB4, 0x24, 0x28, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x10fc92) (leaR64Effect 0x10fc92 6 (.sib 4 none 0 (.d32 0x228)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x10fc92 6 (.sib 4 none 0 (.d32 0x228))).toInstrSpec (lea_r64_effect_step 0x10fc92 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x228)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10fc9a [0x48, 0x8B, 0x1C, 0x24] (LoadPre 0x10fc9a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fc9a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fc9a 3 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10fc9a 3 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x10fc9a 0x48 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10fc9e [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10fc9e) (movR64R64Effect 0x10fc9e 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10fc9e 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10fc9e 0x48 0xdf (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10fca1 [0xE8, 0xFA, 0x03, 0x00, 0x00] (PushPre 0x10fca1 5) (callEffect (fun _ => 0x1100a0) 0x10fca6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10fca1 0x1100a0 0x10fca6).toInstrSpec (call_rel32_effect_step 0x10fca1 0x3fa (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc6a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc72) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc7a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc86) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc92) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc9a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 61), (4, 4), (5, 5), (6, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fc9e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 61), (4, 4), (5, 5), (6, 59), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fca1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 61), (4, 65), (5, 5), (6, 59), (7, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1100a0) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l10fc62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fc62 :=
  Rest.liftedBlock (rest_l10fc62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fc62 x hx)

theorem rest_l10fca6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10fca6 bytes_l10fca6) (entryMap (live .l10fca6))
      9 0x10fca6 bytes_l10fca6 b_l10fca6 := by
  have f0 : InstrSpec 0x10fca6 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x10fca6) (movR64R64Effect 0x10fca6 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x10fca6 0 3).toInstrSpec (mov_r64_r64_effect_step 0x10fca6 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10fca9 [0x48, 0x81, 0xC4, 0xA8, 0x28, 0x00, 0x00] (fun s => s.RIP = 0x10fca9) (addR64Imm32Effect 0x10fca9 4 0x28a8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x10fca9 4 0x28a8).toInstrSpec (add_r64_imm32_effect_step 0x10fca9 0x48 0xc4 0x28a8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10fcb0 [0x5B] (PopPre 0x10fcb0) (popR64Effect 0x10fcb0 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fcb0 1 3).toInstrSpec (pop_r64_effect_step 0x10fcb0 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x10fcb1 [0x41, 0x5C] (PopPre 0x10fcb1) (popR64Effect 0x10fcb1 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fcb1 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10fcb1 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x10fcb3 [0x41, 0x5D] (PopPre 0x10fcb3) (popR64Effect 0x10fcb3 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fcb3 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10fcb3 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x10fcb5 [0x41, 0x5E] (PopPre 0x10fcb5) (popR64Effect 0x10fcb5 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fcb5 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10fcb5 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10fcb7 [0x41, 0x5F] (PopPre 0x10fcb7) (popR64Effect 0x10fcb7 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fcb7 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10fcb7 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x10fcb9 [0x5D] (PopPre 0x10fcb9) (popR64Effect 0x10fcb9 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10fcb9 1 5).toInstrSpec (pop_r64_effect_step 0x10fcb9 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x10fcba [0xC3] (RetPre 0x10fcba) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10fcba).toInstrSpec (ret_effect_step 0x10fcba) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fca9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcb0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcb1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcb3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcb5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcb7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcb9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10fcba) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l10fca6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10fca6 :=
  Rest.liftedBlock (rest_l10fca6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10fca6 x hx)

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

theorem_by block_l10fb20_eval :
    program.runBlock (dialect code) ⟨.l10fb20, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fb7f_eval :
    program.runBlock (dialect code) ⟨.l10fb7f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fb8b_eval :
    program.runBlock (dialect code) ⟨.l10fb8b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fba8_eval :
    program.runBlock (dialect code) ⟨.l10fba8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fbc2_eval :
    program.runBlock (dialect code) ⟨.l10fbc2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fbd5_eval :
    program.runBlock (dialect code) ⟨.l10fbd5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fbee_eval :
    program.runBlock (dialect code) ⟨.l10fbee, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fbfa_eval :
    program.runBlock (dialect code) ⟨.l10fbfa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fc13_eval :
    program.runBlock (dialect code) ⟨.l10fc13, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fc29_eval :
    program.runBlock (dialect code) ⟨.l10fc29, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fc3c_eval :
    program.runBlock (dialect code) ⟨.l10fc3c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fc4f_eval :
    program.runBlock (dialect code) ⟨.l10fc4f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fc62_eval :
    program.runBlock (dialect code) ⟨.l10fc62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10fca6_eval :
    program.runBlock (dialect code) ⟨.l10fca6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Verify.LIR
