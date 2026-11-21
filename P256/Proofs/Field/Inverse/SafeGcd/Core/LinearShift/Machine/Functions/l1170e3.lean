import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Functions.l1170e3_1
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1170e3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111603 bytes_l1170e3) (entryMap (live .l1170e3))
      39 0x111603 bytes_l1170e3 b_l1170e3 := by
  have f0 : InstrSpec 0x111603 [0x48, 0x8B, 0x14, 0x24] (LoadPre 0x111603 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111603 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111603 2 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x111603 2 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x111603 0x48 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x111607 [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x111607 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111607 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111607 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x111607 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x111607 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x11160c [0x48, 0x8B, 0x7C, 0x24, 0x10] (LoadPre 0x11160c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11160c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11160c 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x11160c 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11160c 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x111611 [0x4C, 0x8B, 0x44, 0x24, 0x18] (LoadPre 0x111611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111611 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111611 8 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x111611 8 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x111611 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x111616 [0x4C, 0x8B, 0x5C, 0x24, 0x20] (LoadPre 0x111616 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111616 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111616 11 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x111616 11 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x111616 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11161b [0x89, 0xC1] (fun s => s.RIP = 0x11161b) (movR32R32Effect 0x11161b 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x11161b 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x11161b 0xc1 (by decide)) pre_rip
  have f6 : InstrSpec 0x11161d [0x49, 0xD3, 0xE3] (fun s => s.RIP = 0x11161d) (shlR64ClEffect 0x11161d 3 11)
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x11161d 3 11).toInstrSpec (shl_r64_cl_effect_step 0x11161d 0x49 0xe3 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111620 [0x4D, 0x89, 0xC1] (fun s => s.RIP = 0x111620) (movR64R64Effect 0x111620 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x111620 9 8).toInstrSpec (mov_r64_r64_effect_step 0x111620 0x4d 0xc1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111623 [0x89, 0xE9] (fun s => s.RIP = 0x111623) (movR32R32Effect 0x111623 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111623 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x111623 0xe9 (by decide)) pre_rip
  have f9 : InstrSpec 0x111625 [0x49, 0xD3, 0xE9] (fun s => s.RIP = 0x111625) (shrR64ClEffect 0x111625 3 9)
      [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x111625 3 9).toInstrSpec (shr_r64_cl_effect_step 0x111625 0x49 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111628 [0x89, 0xC1] (fun s => s.RIP = 0x111628) (movR32R32Effect 0x111628 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111628 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x111628 0xc1 (by decide)) pre_rip
  have f11 : InstrSpec 0x11162a [0x49, 0xD3, 0xE0] (fun s => s.RIP = 0x11162a) (shlR64ClEffect 0x11162a 3 8)
      [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x11162a 3 8).toInstrSpec (shl_r64_cl_effect_step 0x11162a 0x49 0xe0 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11162d [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x28] (LoadPre 0x11162d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11162d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x11162d 6 10 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x11162d 6 10 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x11162d 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x111633 [0x4D, 0x09, 0xD9] (fun s => s.RIP = 0x111633) (orR64R64Effect 0x111633 9 11)
      [.gpr 9, .gpr 11] [] [.reg 9, .flags, .rip] :=
    (orR64R64Effect_footprint 0x111633 9 11).toInstrSpec (or_r64_r64_effect_step 0x111633 0x4d 0xd9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111636 [0x49, 0x89, 0xFB] (fun s => s.RIP = 0x111636) (movR64R64Effect 0x111636 11 7)
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR64R64Effect_footprint 0x111636 11 7).toInstrSpec (mov_r64_r64_effect_step 0x111636 0x49 0xfb (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x111639 [0x89, 0xE9] (fun s => s.RIP = 0x111639) (movR32R32Effect 0x111639 2 1 5)
      [.gpr 5] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x111639 2 1 5).toInstrSpec (mov_r32_r32_effect_step 0x111639 0xe9 (by decide)) pre_rip
  have f16 : InstrSpec 0x11163b [0x49, 0xD3, 0xEB] (fun s => s.RIP = 0x11163b) (shrR64ClEffect 0x11163b 3 11)
      [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR64ClEffect_footprint 0x11163b 3 11).toInstrSpec (shr_r64_cl_effect_step 0x11163b 0x49 0xeb (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11163e [0x89, 0xC1] (fun s => s.RIP = 0x11163e) (movR32R32Effect 0x11163e 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x11163e 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x11163e 0xc1 (by decide)) pre_rip
  have f18 : InstrSpec 0x111640 [0x48, 0xD3, 0xE7] (fun s => s.RIP = 0x111640) (shlR64ClEffect 0x111640 3 7)
      [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR64ClEffect_footprint 0x111640 3 7).toInstrSpec (shl_r64_cl_effect_step 0x111640 0x48 0xe7 (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x111643 [0x49, 0x89, 0xF6] (fun s => s.RIP = 0x111643) (movR64R64Effect 0x111643 14 6)
      [.gpr 6] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x111643 14 6).toInstrSpec (mov_r64_r64_effect_step 0x111643 0x49 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111607) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11160c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111611) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111616) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (11, 61), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11161b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (11, 61), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11161d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111620) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 63), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 67), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111623) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 67), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111625) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 71), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111628) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 59), (9, 71), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11162a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 71), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11162d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 71), (10, 77), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111633) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 65), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111636) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 73), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 81), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111639) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 83), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 81), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11163b) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 83), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11163e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 57), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111640) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111643) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 87), (2, 53), (3, 3), (4, 4), (5, 5), (6, 55), (7, 89), (8, 75), (9, 79), (10, 77), (11, 85), (12, 12), (13, 13), (14, 91), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111646) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1170e3_1 code

theorem block_l1170e3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1170e3 :=
  Rest.liftedBlock (rest_l1170e3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1170e3 x hx)
end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
