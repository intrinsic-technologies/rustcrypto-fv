import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Program
import P256.Proofs.Common.Lift.Generated.Values

import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Correction.l1182a7_1

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1182a7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1127c7 bytes_l1182a7) (entryMap (live .l1182a7))
      23 0x1127c7 bytes_l1182a7 b_l1182a7 := by
  have f0 : InstrSpec 0x1127c7 [0x0F, 0xB6, 0x4C, 0x24, 0x07] (LoadPre 0x1127c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127c7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1127c7 5 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x1127c7 5 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x1127c7 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1127cc [0x4D, 0x31, 0xD3] (fun s => s.RIP = 0x1127cc) (xorR64R64Effect 0x1127cc 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1127cc 11 10).toInstrSpec (xor_r64_r64_effect_step 0x1127cc 0x4d 0xd3 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1127cf [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x1127cf) (negR64Effect 0x1127cf 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x1127cf 1).toInstrSpec (neg_r64_effect_step 0x1127cf 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1127d2 [0x4C, 0x21, 0xD9] (fun s => s.RIP = 0x1127d2) (andR64R64Effect 0x1127d2 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1127d2 1 11).toInstrSpec (and_r64_r64_effect_step 0x1127d2 0x4c 0xd9 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1127d5 [0x4C, 0x31, 0xD1] (fun s => s.RIP = 0x1127d5) (xorR64R64Effect 0x1127d5 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1127d5 1 10).toInstrSpec (xor_r64_r64_effect_step 0x1127d5 0x4c 0xd1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1127d8 [0x88, 0x54, 0x24, 0x07] (StorePre 0x1127d8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127d8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1127d8 4 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1127d8 4 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1127d8 2 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1127dc [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x1127dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127dc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1127dc 6 10 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x1127dc 6 10 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x1127dc 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1127e2 [0x4C, 0x31, 0xCE] (fun s => s.RIP = 0x1127e2) (xorR64R64Effect 0x1127e2 6 9)
      [.gpr 6, .gpr 9] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1127e2 6 9).toInstrSpec (xor_r64_r64_effect_step 0x1127e2 0x4c 0xce (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1127e5 [0x49, 0xF7, 0xDA] (fun s => s.RIP = 0x1127e5) (negR64Effect 0x1127e5 10)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (negR64Effect_footprint 0x1127e5 10).toInstrSpec (neg_r64_effect_step 0x1127e5 0x49 0xda (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1127e8 [0x49, 0x21, 0xF2] (fun s => s.RIP = 0x1127e8) (andR64R64Effect 0x1127e8 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1127e8 10 6).toInstrSpec (and_r64_r64_effect_step 0x1127e8 0x49 0xf2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1127eb [0x4D, 0x31, 0xCA] (fun s => s.RIP = 0x1127eb) (xorR64R64Effect 0x1127eb 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1127eb 10 9).toInstrSpec (xor_r64_r64_effect_step 0x1127eb 0x4d 0xca (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1127ee [0x88, 0x54, 0x24, 0x07] (StorePre 0x1127ee 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127ee + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1127ee 4 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1127ee 4 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1127ee 2 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1127f2 [0x0F, 0xB6, 0x74, 0x24, 0x07] (LoadPre 0x1127f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127f2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1127f2 5 6 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x1127f2 5 6 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x1127f2 6 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1127f7 [0x4C, 0x31, 0xC3] (fun s => s.RIP = 0x1127f7) (xorR64R64Effect 0x1127f7 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1127f7 3 8).toInstrSpec (xor_r64_r64_effect_step 0x1127f7 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1127fa [0x48, 0xF7, 0xDE] (fun s => s.RIP = 0x1127fa) (negR64Effect 0x1127fa 6)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (negR64Effect_footprint 0x1127fa 6).toInstrSpec (neg_r64_effect_step 0x1127fa 0x48 0xde (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1127fd [0x48, 0x21, 0xDE] (fun s => s.RIP = 0x1127fd) (andR64R64Effect 0x1127fd 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1127fd 6 3).toInstrSpec (and_r64_r64_effect_step 0x1127fd 0x48 0xde (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x112800 [0x4C, 0x31, 0xC6] (fun s => s.RIP = 0x112800) (xorR64R64Effect 0x112800 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x112800 6 8).toInstrSpec (xor_r64_r64_effect_step 0x112800 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x112803 [0x88, 0x54, 0x24, 0x07] (StorePre 0x112803 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x112803 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x112803 4 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x112803 4 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x112803 2 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x112807 [0x0F, 0xB6, 0x54, 0x24, 0x07] (LoadPre 0x112807 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x112807 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112807 5 2 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x112807 5 2 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x112807 2 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x11280c [0x49, 0x31, 0xC7] (fun s => s.RIP = 0x11280c) (xorR64R64Effect 0x11280c 15 0)
      [.gpr 15, .gpr 0] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11280c 15 0).toInstrSpec (xor_r64_r64_effect_step 0x11280c 0x49 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127cc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127cf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127d2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127d5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127d8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127dc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 64), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127e2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 64), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127e5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 68), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127e8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 70), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127eb) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127ee) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 66), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127f2) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 3), (4, 4), (5, 5), (6, 75), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127f7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 77), (4, 4), (5, 5), (6, 75), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127fa) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 77), (4, 4), (5, 5), (6, 79), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1127fd) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 77), (4, 4), (5, 5), (6, 81), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112800) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 77), (4, 4), (5, 5), (6, 83), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112803) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 61), (2, 2), (3, 77), (4, 4), (5, 5), (6, 83), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112807) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 61), (2, 86), (3, 77), (4, 4), (5, 5), (6, 83), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11280c) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 61), (2, 86), (3, 77), (4, 4), (5, 5), (6, 83), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 88), (22, 22), (39, 39), (51, 51)]) (p' := 0x11280f) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1182a7_1 code

theorem block_l1182a7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1182a7 :=
  Rest.liftedBlock (rest_l1182a7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1182a7 x hx)

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
