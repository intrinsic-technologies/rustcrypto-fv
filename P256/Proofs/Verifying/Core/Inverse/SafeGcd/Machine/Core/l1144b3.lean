import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Core.l1144b3_1
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1144b3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112463 bytes_l1144b3) (entryMap (live .l1144b3))
      22 0x112463 bytes_l1144b3 b_l1144b3 := by
  have f0 : InstrSpec 0x112463 [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x112463) (addR64Imm8Effect 0x112463 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x112463 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x112463 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112467 [0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x112467 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x112467 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112467 0 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112467 0 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x112467 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11246f [0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11246f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x11246f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11246f 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11246f 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11246f 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f3 : InstrSpec 0x112477 [0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x112477 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x112477 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112477 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112477 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x112477 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11247f [0x48, 0x89, 0x44, 0x24, 0x78] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11247f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x11247f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11247f 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11247f 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11247f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f5 : InstrSpec 0x112484 [0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x112484 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x112484 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112484 0 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112484 0 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x112484 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11248c [0x48, 0x89, 0x44, 0x24, 0x70] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11248c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11248c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11248c 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11248c 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11248c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f7 : InstrSpec 0x112491 [0x48, 0x8B, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x112491 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x112491 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112491 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112491 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x112491 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x112499 [0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x112499 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x112499 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112499 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x112499 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x112499 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1124a1 [0x48, 0x89, 0x4C, 0x24, 0x68] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1124a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1124a1 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1124a1 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1124a1 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1124a6 [0x48, 0x89, 0x44, 0x24, 0x60] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124a6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1124a6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1124a6 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1124a6 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1124a6 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1124ab [0x48, 0x8D, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1124ab) (leaR64Effect 0x1124ab 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1124ab 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (lea_r64_effect_step 0x1124ab 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1124b3 [0x48, 0x8B, 0x02] (LoadPre 0x1124b3 (fun s => AddrMode.addr (.base 2 .none) s (0x1124b3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1124b3 0 (.base 2 .none))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1124b3 0 (.base 2 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1124b3 0x48 (by decide) 0 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1124b6 [0x48, 0x8B, 0x4A, 0x08] (LoadPre 0x1124b6 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1124b6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1124b6 1 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1124b6 1 (.base 2 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1124b6 0x48 (by decide) 1 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1124ba [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124ba 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1124ba + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1124ba 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1124ba 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1124ba 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1124c2 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1124c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1124c2 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1124c2 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1124c2 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1124ca [0x48, 0x8B, 0x42, 0x10] (LoadPre 0x1124ca (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1124ca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1124ca 0 (.base 2 (.d8 0x10)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1124ca 0 (.base 2 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1124ca 0x48 (by decide) 0 (.base 2 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1124ce [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124ce 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1124ce + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1124ce 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1124ce 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1124ce 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1124d6 [0x48, 0x8B, 0x42, 0x18] (LoadPre 0x1124d6 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1124d6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1124d6 0 (.base 2 (.d8 0x18)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1124d6 0 (.base 2 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1124d6 0x48 (by decide) 0 (.base 2 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1124da [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1124da 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1124da + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1124da 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1124da 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x1124da 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112467) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11246f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112477) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11247f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112484) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11248c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112491) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112499) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124a1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124a6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124ab) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 64), (1, 66), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124b3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 66), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124b6) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124ba) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 72), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124c2) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 72), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124ca) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124ce) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124d6) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124da) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 74), (2, 70), (3, 3), (4, 53), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1124e2) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l1144b3_1 code

theorem block_l1144b3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1144b3 :=
  Rest.liftedBlock (rest_l1144b3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1144b3 x hx)

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

theorem_by block_l1144b3_eval :
    program.runBlock (dialect code) ⟨.l1144b3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
